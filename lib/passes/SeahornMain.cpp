/// Main Seahorn Pass that kicks everything off


#include "seahorn/SeahornMain.hpp"
#include "ufo/Passes/NameValues.hpp"

#include "llvm/Support/raw_ostream.h"
#include "llvm/IR/Module.h"
#include "llvm/IR/Function.h"
#include "llvm/Transforms/Utils/UnifyFunctionExitNodes.h"
#include "llvm/Support/CFG.h"
#include "llvm/Analysis/CFG.h"
#include "llvm/Support/CommandLine.h"

#include "seahorn/BoostLlvmGraphTraits.hh"

#include "boost/range.hpp"
#include "boost/scoped_ptr.hpp"

#include "seahorn/SymStore.hh"
#include "seahorn/SortTopo.hh"
#include "seahorn/LiveSymbols.hh"

#include "seahorn/Analysis/CutPointGraph.hh"
#include "ufo/Smt/EZ3.hh"

#include "seahorn/HornifyFunction.hh"

#include "ufo/Stats.hh"

using namespace llvm;
using namespace seahorn;
using namespace ufo;

namespace {enum Sem {UFOSMALL, UFOLARGE};}

static llvm::cl::opt<enum Sem>
Semantics("KILLED-horn-sem",
          llvm::cl::desc ("Horn semantics to use for encoding"),
          cl::values (clEnumVal (UFOSMALL, "UFO Small Step"),
                      clEnumVal (UFOLARGE, "UFO Large Step"),
                      clEnumValEnd),
          cl::Hidden,
          cl::init (UFOSMALL));

// option for verification
static llvm::cl::opt<bool>
Verification("KILLED-horn-verify",
             cl::Hidden,
             llvm::cl::desc ("Run pdr/spacer engine (Default: just do compilation)"));


// option for disable inlining
static llvm::cl::opt<bool>
PP("horn-enable-pp",llvm::cl::desc ("Enable pre-processing"));

static llvm::cl::opt<enum TrackLevel>
Track ("KILLED-horn-track-lvl",
       llvm::cl::desc ("Track level for symbolic execution"),
       cl::values (clEnumVal (REG, "Primitive registers only"),
                   clEnumVal (PTR, "REG + pointers"),
                   clEnumVal (MEM, "PTR + memory content"),
                   clEnumValEnd),
       cl::init (MEM), cl::Hidden);

namespace seahorn
{
  //llvm::RegisterPass<SeahornMain> X ("seahorn", "SeaHorn main pass");

  char SeahornMain::ID = 0;

  bool SeahornMain::runOnModule (llvm::Module &M)
  {
    LOG("seahorn", errs () << "Processing a module\n");
    for (auto &F : M) 
      runOnFunction (F, false); 
    return false;
  }


  bool SeahornMain::runOnFunction (llvm::Function &F, bool IkosInvEnabled)
  {
    Function* f = &F;
    if (!F.getName ().startswith ("main")) return false;

    LOG("seahorn", errs () << "Processing Function: " << F.getName () << "\n");
    LOG("seahorn", errs () << "Number of nodes: " << boost::num_vertices (f) << "\n");
    for (llvm::BasicBlock& node : boost::make_iterator_range (boost::vertices (f)))
        LOG ("seahorn", errs () << "Got block: " << node << "\n");

    // -- skip functions without a body
    if (F.isDeclaration () || F.empty ()) return false;

    if (!::findErrorBlock (F))
    {
      if (Verification)
      {
          LOG("seahorn", errs () << "Main does not return\n");
          errs() << "BRUNCH_STAT Result TRUE";
      }
      return false;
    }

    //CutPointGraph &cpg = getAnalysis<CutPointGraph> (F);
    ExprFactory efac;
    EZ3 ctx (efac); // Z3 context wrapper
    ZFixedPoint<EZ3> fp (ctx); // Z3 fixpoint

    if (!PP) {
        LOG ("seahorn", errs() << "... pre-processing is disabled \n");
        ZParams<EZ3> params (ctx);
        params.set (":engine", "pdr");
        params.set (":use-farkas", true);
        params.set (":generate-proof-trace", false);
        params.set (":slice", false);
        params.set (":inline-linear", false);
        params.set (":inline-eager", false);
        fp.set (params);
    }

    if (IkosInvEnabled)
    {
      // If Covers are used then Z3 requires slicing to be disabled
      ZParams<EZ3> fp_opts(ctx);
      fp_opts.set("slice",false);
      fp.set(fp_opts);
    }

    DataLayout &td = getAnalysis<DataLayout> ();
    
    boost::scoped_ptr<SmallStepSymExec> ssem (new UfoSmallSymExec (efac, td, Track));

    boost::scoped_ptr<HornifyFunction> horn;
    
    // XXX Killed. Will be called from HornifyModule instead
    // if (Semantics == UFOSMALL)
    //   horn.reset (new SmallHornifyFunction (m_hm));
    // else if (Semantics == UFOLARGE)
    //   horn.reset (new LargeHornifyFunction (m_hm));

    Stats::start ("hornification");
    LiveSymbols ls (F, efac, *ssem);
    ls();
    
    horn->runOnFunction (F);
    Stats::stop ("hornification");
    m_out << fp << "\n";
    if (Verification) {
        LOG("seahorn", errs() << "... verification is enabled.\n");
        //ExprVector prop = horn->getPredicates();
        Expr cex;
        //horn->checkProperty(prop,cex);  // commented for the competition
        Stats::resume ("verification");
        //horn->getResult(cex);
        Stats::stop("verification");
        Stats::PrintBrunch (errs ());
        errs ().flush ();
    }
    return false;
  }

  void SeahornMain::getAnalysisUsage (llvm::AnalysisUsage &AU) const
  {
    AU.setPreservesAll ();
    AU.addRequired<llvm::DataLayout>();
    AU.addRequired<ufo::NameValues>();
    AU.addRequired<seahorn::TopologicalOrder>();
    AU.addRequired<seahorn::CutPointGraph>();
  }

}
