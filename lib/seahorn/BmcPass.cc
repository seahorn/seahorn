#include "llvm/Analysis/CallGraph.h"
#include "llvm/Analysis/PostDominators.h"
#include "llvm/Analysis/TargetLibraryInfo.h"
#include "llvm/Bitcode/BitcodeWriter.h"
#include "llvm/IR/Dominators.h"
#include "llvm/IR/Function.h"
#include "llvm/IR/InstIterator.h"
#include "llvm/IR/Instructions.h"
#include "llvm/IR/Module.h"
#include "llvm/IR/Verifier.h"
#include "llvm/Pass.h"
#include "llvm/Support/FileSystem.h"
#include "llvm/Support/raw_ostream.h"
#include "llvm/Support/ToolOutputFile.h"

#include "seahorn/config.h"
#include "seahorn/Support/Stats.hh"
#include "seahorn/Transforms/Utils/NameValues.hh"
#include "seahorn/Analysis/CanFail.hh"
#include "seahorn/Analysis/ControlDependenceAnalysis.hh"
#include "seahorn/Analysis/GateAnalysis.hh"
#include "seahorn/Bmc.hh"
#include "seahorn/CexHarness.hh"
#include "seahorn/BvOpSem.hh"
#include "seahorn/BvOpSem2.hh"
#include "seahorn/DfCoiAnalysis.hh"
#include "seahorn/PathBmc.hh"
#include "seahorn/Support/SeaDebug.h"
#include "seahorn/Support/SeaLog.hh"

#include "sea_dsa/AllocWrapInfo.hh"

namespace seahorn {
// defined in HornCex.cc
extern std::string HornCexFile;
}

// XXX temporary debugging aid
static llvm::cl::opt<bool> HornBv2("horn-bv2",
                                   llvm::cl::desc("Use bv2 semantics"),
                                   llvm::cl::init(false), llvm::cl::Hidden);

static llvm::cl::opt<bool> HornGSA("horn-gsa",
                                   llvm::cl::desc("Use Gated SSA for bmc"),
                                   llvm::cl::init(false), llvm::cl::Hidden);

static llvm::cl::opt<bool> ComputeCoi("horn-bmc-coi",
                                      llvm::cl::desc("Compute DataFlow-based COI"),
                                      llvm::cl::init(false), llvm::cl::Hidden);

namespace {
using namespace llvm;
using namespace seahorn;

class BmcPass : public llvm::ModulePass {
public:
  // Available BMC engines
  enum class BmcEngineKind {
    mono_bmc,
    path_bmc
  };

private:
  /// bmc engine type
  BmcEngineKind m_engine;
  /// output stream for encoded bmc problem
  raw_ostream *m_out;
  /// true if to run the solver, false if encode only
  bool m_solve;
  /// can-fail analysis
  CanFail *m_failure_analysis;

  GateAnalysis *m_gsa;

public:
  static char ID;

  BmcPass(BmcEngineKind engine = BmcEngineKind::mono_bmc, raw_ostream *out = nullptr,
          bool solve = true)
      : llvm::ModulePass(ID), m_engine(engine), m_out(out), m_solve(solve),
        m_failure_analysis(nullptr) {}

  virtual bool runOnModule(Module &M) {
    LOG("bmc-pass", errs() << "Start BmcPass\n";);
    m_failure_analysis = getAnalysisIfAvailable<CanFail>();

    Function *main = M.getFunction("main");
    if (!main || main->isDeclaration()) {
      errs() << "WARNING: The program has no main() function.\n";
      errs() << "WARNING: Possibly all assertions have been "
             << "discharged by the front-end\n";
      errs() << "WARNING: Alternatively, use --entry ENTRY option to specify a"
             << "custom entry point\n";
      return false;
    }

    m_gsa = HornGSA ? &getAnalysis<GateAnalysisPass>().getGateAnalysis(*main)
                    : nullptr;

    return runOnFunction(*main);
  }

  void getAnalysisUsage(AnalysisUsage &AU) const {
    AU.addRequired<TargetLibraryInfoWrapperPass>();
    AU.addRequired<sea_dsa::AllocWrapInfo>();
    AU.addRequired<CallGraphWrapperPass>();    
    
    AU.addRequired<CanFail>();
    AU.addRequired<NameValues>();
    AU.addRequired<TopologicalOrder>();
    AU.addRequired<CutPointGraph>();

    if (HornGSA)
      AU.addRequired<GateAnalysisPass>();

    AU.setPreservesAll();
  }

  bool runOnFunction(Function &F) {
    LOG("bmc-pass", errs() << "Starting BMC on " << F.getName() << "\n";);
    LOG("bmc.dumpf", errs() << F << "\n");
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
      ERR << "Function " << F.getName()
          << " does not have a unique return block"
             "This is not expected during BMC. Aborting.";
      return false;
    }

    if (!cpg.getEdge(src, *dst)) {
      ERR << "No direct entry-to-exit path in " << F.getName() << ". "
          << "Commonly caused by loops. Ensure the input to BMC is loop-free";

      LOG("cpg_bmc", cpg.print(llvm::errs(), F.getParent()));
      return false;
    }

    ExprFactory efac;

    if (m_engine == BmcEngineKind::mono_bmc) {

      std::unique_ptr<OperationalSemantics> sem;
      if (HornBv2)
        sem = llvm::make_unique<Bv2OpSem>(efac, *this,
                                          F.getParent()->getDataLayout(), MEM);
      else
        sem = llvm::make_unique<BvOpSem>(efac, *this,
                                         F.getParent()->getDataLayout(), MEM);

      if(ComputeCoi) {
	computeCoi(F, *sem);
      }
      
      EZ3 zctx(efac);
      // XXX: uses OperationalSemantics but trace generation still depends on
      // LegacyOperationalSemantics
      BmcEngine bmc(*sem, zctx);

      bmc.addCutPoint(src);
      bmc.addCutPoint(*dst);
      LOG("bmc", errs() << "BMC from: " << src.bb().getName() << " to "
                        << dst->bb().getName() << "\n";);

      Stats::resume("BMC");
      bmc.encode();

      Stats::uset("bmc.dag_sz", dagSize(bmc.getFormula()));
      Stats::uset("bmc.circ_sz", boolop::circSize(bmc.getFormula()));

      LOG("bmc.simplify",
          // --
          Expr vc = mknary<AND>(bmc.getFormula());
          Expr vc_simpl = z3_simplify(bmc.zctx(), vc);
          llvm::errs() << "VC:\n"
                       << z3_to_smtlib(bmc.zctx(), vc) << "\n~~~~\n"
                       << "Simplified VC:\n"
                       << z3_to_smtlib(bmc.zctx(), vc_simpl) << "\n");

      if (m_out)
        bmc.toSmtLib(*m_out);

      if (!m_solve) {
        LOG("bmc", errs() << "Stopping before solving\n";);
        Stats::stop("BMC");
        return false;
      }

      auto res = bmc.solve();
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

      LOG("bmc_core",
          // producing bmc core is expensive. Enable only if specifically
          // requested
          if (!res) {
            ExprVector core;
            bmc.unsatCore(core);
            errs() << "CORE BEGIN\n";
            for (auto c : core)
              errs() << *c << "\n";
            errs() << "CORE END\n";
          });


      
      LOG("cex", if (res) {
	  errs() << "Analyzed Function:\n" << F << "\n";
	  errs() << "Trace \n";
	  BmcTrace trace(bmc.getTrace());	  
	  trace.print(errs());
	});

      if (res) {
	StringRef CexFileRef(HornCexFile);
	if (CexFileRef != "") {
	  if (CexFileRef.endswith(".ll") || CexFileRef.endswith(".bc")) {
	    auto const &tli = getAnalysis<TargetLibraryInfoWrapperPass>().getTLI();	
	    auto const &dl = F.getParent()->getDataLayout();
	    BmcTrace trace(bmc.getTrace());	  	  
	    BmcTraceWrapper trace_wrapper(trace);
	    dumpLLVMCex(trace_wrapper, CexFileRef, dl, tli, F.getContext());
	  } else {
	    WARN << "The Bmc engine only generates harnesses in bitcode format";
	  }
	}
      }
    } else if (m_engine == BmcEngineKind::path_bmc) {

      auto const &dl = F.getParent()->getDataLayout();      
      std::unique_ptr<OperationalSemantics> sem = llvm::make_unique<BvOpSem>(
          efac, *this, dl, MEM);

      // XXX: needed by sea-dsa which is required by clam      
      auto const &tli = getAnalysis<TargetLibraryInfoWrapperPass>().getTLI();
      auto &cg = getAnalysis<CallGraphWrapperPass>().getCallGraph();      
      auto &awi = getAnalysis<sea_dsa::AllocWrapInfo>();      
      
      // XXX: use of legacy operational semantics
      PathBmcEngine bmc(static_cast<LegacyOperationalSemantics &>(*sem),
			dl, tli, cg, awi);
      
      bmc.addCutPoint(src);
      bmc.addCutPoint(*dst);
      LOG("bmc", errs() << "Path BMC from: " << src.bb().getName() << " to "
                        << dst->bb().getName() << "\n";);

      Stats::resume("BMC");

      if (!m_solve) {
        LOG("bmc", errs() << "Stopping before solving\n";);
        Stats::stop("BMC");
        return false;
      }

      auto res = bmc.solve();
      Stats::stop("BMC");

      if (res == solver::SolverResult::SAT)
        outs() << "sat";
      else if (res == solver::SolverResult::UNSAT)
        outs() << "unsat";
      else
        outs() << "unknown";
      outs() << "\n";

      if (res == solver::SolverResult::SAT)
        Stats::sset("Result", "FALSE");
      else if (res == solver::SolverResult::UNSAT)
        Stats::sset("Result", "TRUE");

      LOG("cex", if (res == solver::SolverResult::SAT) {
        errs() << "Analyzed Function:\n" << F << "\n";
        PathBmcTrace trace(bmc.getTrace());
        errs() << "Trace \n";
        trace.print(errs());
      });

      // TODO: generate a harness from PathBmcTrace
    }
    return false;
  }

  StringRef getPassName() const override { return "BmcPass"; }


  void computeCoi(Function &F, OperationalSemantics &sem) {
    DfCoiAnalysis dfCoi;

    Module *m = F.getParent();
    assert(m);
    // -- compute dependnece of verifier.assume()
    Function *assumeFn = m->getFunction("verifier.assume");
    if(assumeFn) {
      for (auto *u : assumeFn->users()) {
        if (auto *CI = dyn_cast<CallInst>(u)) {
          CallSite CS(CI);
          if (CS.getCaller() != &F) continue;
          dfCoi.analyze(*CI);
        }
      }
    }

    // -- compute dependence of verifier.assume.not()
    assumeFn = m->getFunction("verifier.assume.not");
    if (assumeFn) {
      for (auto *u : assumeFn->users()) {
        if (auto *CI = dyn_cast<CallInst>(u)) {
          CallSite CS(CI);
          if (CS.getCaller() != &F)
            continue;
          dfCoi.analyze(*CI);
        }
      }
    }

    // install dependence filter in operational semantics
    auto &filter = dfCoi.getCoi();
    sem.addToFilter(filter.begin(), filter.end());
  }
};

char BmcPass::ID = 0;
} // namespace
namespace seahorn {
Pass *createBmcPass(raw_ostream *out, bool solve) {
  return new BmcPass(BmcPass::BmcEngineKind::mono_bmc, out, solve);
}
Pass *createPathBmcPass(raw_ostream *out, bool solve) {
  return new BmcPass(BmcPass::BmcEngineKind::path_bmc, out, solve);
}

} // namespace seahorn

static llvm::RegisterPass<BmcPass> X("bmc-pass", "Run BMC engine");
