#include "seahorn/Analysis/CrabAnalysis.hh"
#include "seahorn/Analysis/SeaBuiltinsInfo.hh"
#include "seahorn/Passes.hh"
#include "seahorn/Support/SeaDebug.h"
#include "seahorn/Support/SeaLog.hh"
#include "seahorn/Support/Stats.hh"

#include "llvm/Analysis/CallGraph.h"
#include "llvm/Analysis/TargetLibraryInfo.h"
#include "llvm/IR/DebugInfo.h"
#include "llvm/IR/DebugLoc.h"

#include "seadsa/AllocWrapInfo.hh"
#include "seadsa/DsaLibFuncInfo.hh"
#include "seadsa/Global.hh"
#include "seadsa/Graph.hh"

#include "clam/CfgBuilder.hh"
#include "clam/Clam.hh"

using namespace llvm;
using namespace seahorn;

namespace {

struct CrabLowerIsDeref : public ModulePass {
private:
  Value *crabLowerIsDereferenceable(CallBase *IsDerefCall);
  const llvm::ConstantRange getCrabInstRng(const llvm::Instruction &I) const;

  clam::InterGlobalClam *m_crab_ptr;

public:
  static char ID;

  CrabLowerIsDeref() : ModulePass(ID) {}

  bool runOnModule(Module &M) override;
  void getAnalysisUsage(AnalysisUsage &AU) const override {
    AU.addRequired<llvm::CallGraphWrapperPass>();
    AU.addRequired<llvm::TargetLibraryInfoWrapperPass>();
    AU.addRequired<seadsa::AllocWrapInfo>();
    AU.addRequired<seadsa::DsaLibFuncInfo>();
    AU.addRequired<SeaBuiltinsInfoWrapperPass>();
    AU.setPreservesAll();
  }
  StringRef getPassName() const override { return "CrabLowerIsDeref"; }
};
char CrabLowerIsDeref::ID = 0;

} // namespace

bool CrabLowerIsDeref::runOnModule(Module &M) {
  LOG("crab-isderef", errs()
                          << "Start Running Crab lowering is_deref checks\n";);
  CrabAnalysis crab = CrabAnalysis();
  const llvm::DataLayout &dl = M.getDataLayout();
  // Get dependent LLVM Passes
  auto &allocInfo = getAnalysis<seadsa::AllocWrapInfo>();
  allocInfo.initialize(M, this);
  auto &dsaLibFuncInfo = getAnalysis<seadsa::DsaLibFuncInfo>();
  dsaLibFuncInfo.initialize(M);
  auto &cg = getAnalysis<CallGraphWrapperPass>().getCallGraph();
  // Get target library info pass
  auto &tliPass = getAnalysis<TargetLibraryInfoWrapperPass>();
  seadsa::Graph::SetFactory setFactory;

  // Get seadsa -- pointer analysis
  seadsa::ContextSensitiveGlobalAnalysis dsa(
      dl, tliPass, allocInfo, dsaLibFuncInfo, cg, setFactory,
      true /* always store summary graphs*/);
  // Run dsa analysis on current module
  dsa.runOnModule(M);
  // Crab required to compute memory info by a DSA-like analysis
  // Sea-DSA is the most common use.
  crab.runCrabAnalysisOnModule(M, dsa, tliPass);
  m_crab_ptr = &crab.getCrab();
  auto &SBI = getAnalysis<SeaBuiltinsInfoWrapperPass>().getSBI();

  bool Changed = false;

  for (auto &F : M) {
    for (auto &BB : F) {
      SmallVector<CallInst *, 32> deadCalls;
      for (auto &I : BB) {
        if (auto *CB = dyn_cast<CallInst>(&I)) {
          if (SBI.getSeaBuiltinOp(*CB) != SeaBuiltinsOp::IS_DEREFERENCEABLE)
            continue;

          // this is a call to sea.is_dereferenceable
          Value *res = crabLowerIsDereferenceable(CB);
          if (res) {
            CB->replaceAllUsesWith(res);
            deadCalls.push_back(CB);
            Changed = true;
          }
        }
      }
      for (auto &DC : deadCalls) {
        DC->eraseFromParent();
      }
    }
  }

  LOG("crab-isderef", errs() << "Crab lowering is_deref checks complete\n";);
  return Changed;
}

const llvm::ConstantRange
CrabLowerIsDeref::getCrabInstRng(const llvm::Instruction &I) const {
  unsigned IntWidth = I.getType()->getIntegerBitWidth();
  return m_crab_ptr->range(I);
}

Value *CrabLowerIsDeref::crabLowerIsDereferenceable(CallBase *IsDerefCall) {

  auto crabDerefResult = getCrabInstRng(*IsDerefCall);
  auto &C = IsDerefCall->getContext();
  if (crabDerefResult.isEmptySet()) {
    // Crab skips is_deref due to invariant inferred along the path is bottom
    // This means the is_deref cannot reach, delete it.
    Stats::count("crab.pp.isderef.solve");
    return ConstantInt::getTrue(C);
  } else if (crabDerefResult.isSingleElement()) {
    // Crab inferred is_deref call is either true or false
    Stats::count("crab.pp.isderef.solve");
    return crabDerefResult.getSingleElement()->getBoolValue()
               ? ConstantInt::getTrue(C)
               : ConstantInt::getFalse(C);
  } else {
    // Crab cannot know the is_deref result
    Stats::count("crab.pp.isderef.not.solve");
    LOG("seapp-crab", const llvm::DebugLoc &dloc = IsDerefCall->getDebugLoc();
        unsigned Line = dloc.getLine(); unsigned Col = dloc.getCol();
        const std::string &File = (*dloc).getFilename();
        MSG << "crab cannot solve: " << *IsDerefCall << " at File=" << File
            << " Line=" << Line << " col=" << Col;);
    return nullptr;
  }
}

llvm::Pass *seahorn::createCrabLowerIsDerefPass() {
  return new CrabLowerIsDeref();
}
