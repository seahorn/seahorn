#include "llvm/Analysis/TargetLibraryInfo.h"
#include "llvm/IR/Function.h"
#include "llvm/IR/Instructions.h"
#include "llvm/IR/Module.h"
#include "llvm/Pass.h"
#include "llvm/Support/raw_ostream.h"

#include "seahorn/config.h"

#include "ufo/Passes/NameValues.hpp"
#include "ufo/Smt/EZ3.hh"
#include "ufo/Stats.hh"

#include "seahorn/Analysis/CanFail.hh"
#include "seahorn/Bmc.hh"
#include "seahorn/BvOpSem.hh"
#include "seahorn/BvOpSem2.hh"
#include "seahorn/PathBasedBmc.hh"
#include "seahorn/UfoOpSem.hh"
// prerequisite for CrabLlvm
#include "seahorn/Transforms/Scalar/LowerCstExpr.hh"
#include "avy/AvyDebug.h"

#ifdef HAVE_CRAB_LLVM
#include "crab_llvm/CrabLlvm.hh"
#endif


// XXX temporary debugging aid
static llvm::cl::opt<bool> HornBv2(
    "horn-bv2",
    llvm::cl::desc("Use bv2 semantics"),
    llvm::cl::init(false), llvm::cl::Hidden);


namespace {
using namespace llvm;
using namespace seahorn;
using namespace ufo;

class BmcPass : public llvm::ModulePass {
  /// bmc engine
  bmc_engine_t m_engine;
  /// output stream for encoded bmc problem
  raw_ostream *m_out;
  /// true if to run the solver, false if encode only
  bool m_solve;
  /// can-fail analysis
  CanFail *m_failure_analysis;

public:
  static char ID;

  BmcPass(bmc_engine_t engine = mono_bmc, raw_ostream *out = nullptr,
          bool solve = true)
      : llvm::ModulePass(ID), m_engine(engine), m_out(out), m_solve(solve),
        m_failure_analysis(nullptr) {}

  virtual bool runOnModule(Module &M) {
    LOG("bmc-pass", errs() << "Start BmcPass\n";);
    m_failure_analysis = getAnalysisIfAvailable<seahorn::CanFail>();

    Function *main = M.getFunction("main");
    if (!main || main->isDeclaration()) {
      errs() << "WARNING: The program has no main() function.\n";
      errs() << "WARNING: Possibly all assertions have been "
             << "discharged by the front-end\n";
      errs() << "WARNING: Alternatively, use --entry ENTRY option to specify a"
             << "custom entry point\n";
      return false;
    }

    return runOnFunction(*main);
  }

  void getAnalysisUsage(AnalysisUsage &AU) const {
    AU.setPreservesAll();

    AU.addRequired<seahorn::CanFail>();
    AU.addRequired<ufo::NameValues>();
    AU.addRequired<seahorn::TopologicalOrder>();
    AU.addRequired<CutPointGraph>();
    AU.addRequired<TargetLibraryInfoWrapperPass>();
#ifdef HAVE_CRAB_LLVM
    AU.addRequired<seahorn::LowerCstExprPass>();
    AU.addRequired<crab_llvm::CrabLlvmPass>();
#endif
  }

  virtual bool runOnFunction(Function &F) {
    LOG("bmc-pass", errs() << "Starting BMC on " << F.getName() << "\n";);
    if (m_failure_analysis) {
      bool canFail = false;
      if (!canFail) {
        // --- optimizer or ms can detect an error and make main
        //     unreachable. In that case, it will insert a call to
        //     seahorn.fail.
        Function *failureFn = F.getParent()->getFunction("seahorn.fail");
        for (auto &I : boost::make_iterator_range(inst_begin(F), inst_end(F))) {
          if (!isa<CallInst>(&I))
            continue;
          // -- look through pointer casts
          Value *v = I.stripPointerCasts();
          CallSite CS(const_cast<Value *>(v));
          const Function *fn = CS.getCalledFunction();
          canFail |= (fn == failureFn);
        }
      }
      if (!canFail) {
        // --- we ask the can-fail analysis if the function can fail.
        canFail |= m_failure_analysis->canFail(&F);
      }

      if (!canFail) {
        errs() << "WARNING: no assertion was found ";
        errs() << "so either program does not have assertions or front-end "
                  "discharged them.\n";
        return false;
      }
    }

    const CutPointGraph &cpg = getAnalysis<CutPointGraph>(F);
    const CutPoint &src = cpg.getCp(F.getEntryBlock());
    const CutPoint *dst = nullptr;

    // -- find return instruction. Assume it is unique
    for (auto &bb : F)
      if (llvm::isa<llvm::ReturnInst>(bb.getTerminator()) &&
          cpg.isCutPoint(bb)) {
        dst = &cpg.getCp(bb);
        break;
      }

    if (dst == nullptr) {
      // cpg.print(llvm::errs (), F.getParent());
      errs() << "WARNING: BmcPass: function '" << F.getName()
             << "' never returns\n";
      return false;
    }

    if (!cpg.getEdge(src, *dst)) {
      // cpg.print(llvm::errs (), F.getParent());
      errs() << "WARNING: BmcPass: function '" << F.getName()
             << "' never returns\n";
      return false;
    }

    ExprFactory efac;

    std::unique_ptr<OpSem> sem;
    if (HornBv2)
      sem.reset(new Bv2OpSem (efac, *this, F.getParent()->getDataLayout(), MEM));
    else
      sem.reset(new BvOpSem(efac, *this, F.getParent()->getDataLayout(), MEM));

    EZ3 zctx(efac);
    std::unique_ptr<BmcEngine> bmc;
    switch (m_engine) {
    case path_bmc: {
      const TargetLibraryInfo &tli =
          getAnalysis<TargetLibraryInfoWrapperPass>().getTLI();
#ifdef HAVE_CRAB_LLVM
      crab_llvm::CrabLlvmPass &crab = getAnalysis<crab_llvm::CrabLlvmPass>();
      bmc.reset(new PathBasedBmcEngine(*sem, zctx, &crab, tli));
#else
      bmc.reset(new PathBasedBmcEngine(*sem, zctx, tli));
#endif
      break;
    }
    case mono_bmc:
    default:
      bmc.reset(new BmcEngine(*sem, zctx));
    }

    bmc->addCutPoint(src);
    bmc->addCutPoint(*dst);
    LOG("bmc", errs() << "BMC from: " << src.bb().getName() << " to "
                      << dst->bb().getName() << "\n";);

    bmc->encode();
    if (m_out)
      bmc->toSmtLib(*m_out);

    if (!m_solve) {
      LOG("bmc", errs() << "Stopping before solving\n";);
      return false;
    }

    Stats::resume("BMC");
    auto res = bmc->solve();
    Stats::stop("BMC");

    if (res)
      outs() << "sat";
    else if (!res)
      outs() << "unsat";
    else
      outs() << "unknown";
    outs() << "\n";

    if (res)
      Stats::sset("Result", "FALSE");
    else if (!res)
      Stats::sset("Result", "TRUE");

    LOG("bmc", if (!res) {
      ExprVector core;
      bmc->unsatCore(core);
      errs() << "CORE BEGIN\n";
      for (auto c : core)
        errs() << *c << "\n";
      errs() << "CORE END\n";
    });

    LOG("cex", if (res) {
      errs() << "Analyzed Function:\n" << F << "\n";
      BmcTrace trace(bmc->getTrace());
      errs() << "Trace \n";
      trace.print(errs());
    });

    return false;
  }

  virtual StringRef getPassName() const { return "BmcPass"; }
};

char BmcPass::ID = 0;
} // namespace
namespace seahorn {
Pass *createBmcPass(bmc_engine_t engine, raw_ostream *out, bool solve) {
  return new BmcPass(engine, out, solve);
}
} // namespace seahorn

static llvm::RegisterPass<BmcPass> X("bmc-pass", "Run BMC engine");
