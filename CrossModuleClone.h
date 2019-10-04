#include "llvm/ADT/Statistic.h"
#include "llvm/IR/Dominators.h"
#include "llvm/IR/InstrTypes.h"
#include "llvm/IR/Function.h"
#include "llvm/Bitcode/BitcodeWriter.h"

#include "llvm/Pass.h"
#include "llvm/Support/raw_ostream.h"

#include "llvm/Transforms/Utils/Cloning.h"

#include <typeinfo>
#include <string>

using namespace llvm;

static cl::opt<std::string> FunctionName("func-extractor-fn-name", cl::init(""), cl::Hidden,
    cl::desc("Name of the function to be extracted"));

static cl::opt<std::string> Path("func-extractor-path", cl::init(""), cl::Hidden,
    cl::desc("Path where the file will be saved"));

static void copyComdat(GlobalObject *Dst, const GlobalObject *Src) {
  const Comdat *SC = Src->getComdat();
  if (!SC)
    return;
  Comdat *DC = Dst->getParent()->getOrInsertComdat(SC->getName());
  DC->setSelectionKind(SC->getSelectionKind());
  Dst->setComdat(DC);
}

void CloneUsedGlobalsAcrossModule(Function *F, Module *M, Module *NewM, ValueToValueMapTy &VMap) {
  std::set<const Value*> NeededValues;

  NeededValues.insert(F);  
  for (Instruction &I : instructions(F)) {
    for (unsigned i = 0; i<I.getNumOperands(); i++) {
      NeededValues.insert(I.getOperand(i));
      NeededValues.insert(&I);
    }
  }

  // Loop over all of the global variables, making corresponding globals in the
  // new module.  Here we add them to the VMap and to the new Module.  We
  // don't worry about attributes or initializers, they will come later.
  //
  for (Module::const_global_iterator I = M->global_begin(), E = M->global_end();
       I != E; ++I) {

    if (VMap.find(&*I)!=VMap.end()) continue;

    //if (UsedValues.find(&*I)==UsedValues.end()) continue;
    bool FoundUse = false;
    for (const User *U : I->users()) {
      if (NeededValues.find(U)!=NeededValues.end()) { FoundUse = true; break; }
    }
    if (!FoundUse) continue;

    GlobalVariable *GV = new GlobalVariable(*NewM,
                                            I->getValueType(),
                                            I->isConstant(), I->getLinkage(),
                                            (Constant*) nullptr, I->getName(),
                                            (GlobalVariable*) nullptr,
                                            I->getThreadLocalMode(),
                                            I->getType()->getAddressSpace());
    GV->copyAttributesFrom(&*I);
    VMap[&*I] = GV;
  }

  // Loop over the functions in the module, making external functions as before
  for (const Function &I : *M) {
    if (VMap.find(&*I)!=VMap.end()) continue;
    if (NeededValues.find(&I)==NeededValues.end() || (&I)==F) continue;
    Function *NF =
        Function::Create(cast<FunctionType>(I.getValueType()), I.getLinkage(),
                         I.getAddressSpace(), I.getName(), NewM);
    NF->copyAttributesFrom(&I);
    VMap[&I] = NF;
  }

  // Loop over the aliases in the module
  for (Module::const_alias_iterator I = M->alias_begin(), E = M->alias_end();
       I != E; ++I) {

    if (VMap.find(&*I)!=VMap.end()) continue;
    if (NeededValues.find(&*I)==NeededValues.end()) continue;
    auto *GA = GlobalAlias::create(I->getValueType(),
                                   I->getType()->getPointerAddressSpace(),
                                   I->getLinkage(), I->getName(), NewM);
    GA->copyAttributesFrom(&*I);
    VMap[&*I] = GA;
  }

  // Now that all of the things that global variable initializer can refer to
  // have been created, loop through and copy the global variable referrers
  // over...  We also set the attributes on the global now.
  //
  for (Module::const_global_iterator I = M->global_begin(), E = M->global_end();
       I != E; ++I) {

    if (I->isDeclaration())
      continue;

    if (VMap[&*I]==nullptr) continue;

    GlobalVariable *GV = dyn_cast<GlobalVariable>(VMap[&*I]);


    if (I->hasInitializer())
      GV->setInitializer(MapValue(I->getInitializer(), VMap));

    SmallVector<std::pair<unsigned, MDNode *>, 1> MDs;
    I->getAllMetadata(MDs);
    for (auto MD : MDs)
      GV->addMetadata(MD.first,
                      *MapMetadata(MD.second, VMap, RF_MoveDistinctMDs));

    copyComdat(GV, &*I);
  }
}

void CloneFunctionAcrossModule(Function *F, Module *M, ValueToValueMapTy &VMap) {

  CloneUsedGlobalsAcrossModule(F,F->getParent(),M,VMap);

  Function *NewF = Function::Create(cast<FunctionType>(F->getValueType()), F->getLinkage(),
                         F->getAddressSpace(), F->getName(), M);
  NewF->copyAttributesFrom(F);
  VMap[F] = NewF;

  Function::arg_iterator DestArg = NewF->arg_begin();
  for (Function::const_arg_iterator Arg = F->arg_begin(); Arg != F->arg_end();
         ++Arg) {
    DestArg->setName(Arg->getName());
    VMap[&*Arg] = &*DestArg++;
  }

  SmallVector<ReturnInst *, 8> Returns; // Ignore returns cloned.
  CloneFunctionInto(NewF, F, VMap, /*ModuleLevelChanges=*/true, Returns);

  if (F->hasPersonalityFn())
    NewF->setPersonalityFn(MapValue(F->getPersonalityFn(), VMap));

  copyComdat(NewF, F);
}

void ExtractFunctionIntoFile(Module &M, std::string FName, std::string FilePath) {
  Function *F = M.getFunction(FName);
  if (F) {
      ValueToValueMapTy VMap;

      std::unique_ptr<Module> NewM =
      std::make_unique<Module>(M.getModuleIdentifier(), M.getContext());

      CloneFunctionAcrossModule(F,&*NewM,VMap);

      std::error_code EC;
      llvm::raw_fd_ostream OS(FilePath, EC, llvm::sys::fs::F_None);
      WriteBitcodeToFile(*NewM, OS);
      OS.flush();
  }
}

namespace llvm {


struct CrossModuleFunctionExtractor : public ModulePass {
  static char ID;

  CrossModuleFunctionExtractor() : ModulePass(ID) {
    initializeCrossModuleFunctionExtractorPass(*PassRegistry::getPassRegistry());
  }

  bool runOnModule(Module &M) override {
    ExtractFunctionIntoFile(M, FunctionName, Path);
  }

  void getAnalysisUsage(AnalysisUsage &AU) const override {
    // We don't modify the program, so we preserve all analyses.
    AU.setPreservesAll();
  }
};

ModulePass *createCrossModuleFunctionExtractorPass() {
  return new CrossModuleFunctionExtractor();
}

} //end namespace

char CrossModuleFunctionExtractor::ID = 0;
INITIALIZE_PASS(CrossModuleFunctionExtractor, "func-extractor", "Extract functions into new module", false, false)


