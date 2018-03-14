#include "seahorn/HornSolver.hh"
#include "seahorn/HornifyModule.hh"
#include "seahorn/HornClauseDBTransf.hh"
#include "seahorn/HornDbModel.hh"

#include "llvm/IR/Function.h"
#include "llvm/Support/CommandLine.h"
#include "ufo/Stats.hh"

#include "boost/range/algorithm/reverse.hpp"

#include <climits>

using namespace llvm;

static llvm::cl::opt<std::string>
PdrEngine ("horn-pdr-engine",
           llvm::cl::desc ("Pdr engine to use"),
           cl::init ("spacer"),
           cl::Hidden);

static llvm::cl::opt<bool>
PrintAnswer ("horn-answer",
             cl::desc ("Print Horn answer"), cl::init (false));

static llvm::cl::opt<bool>
EstimateSizeInvars ("horn-estimate-size-invars",
             cl::desc ("Give an estimation about the size of all inferred invariants"),
             cl::init (false));

static llvm::cl::opt<bool>
SkipConstraints ("horn-skip-constraints",
                 cl::Hidden, cl::init(false),
                 cl::desc ("Enabled when number of predicates exceeds 200"));

static llvm::cl::opt<bool>
Subsumption ("horn-subsumption", cl::Hidden, cl::init(true),
             cl::desc ("Setting to false helps with cex"));

static llvm::cl::opt<bool>
FlexTrace ("horn-flex-trace", cl::Hidden, cl::init (false));

static llvm::cl::opt<bool>
HornChildren ("horn-child-order", cl::Hidden, cl::init(true));

static llvm::cl::opt<unsigned>
PdrContexts ("horn-pdr-contexts", cl::Hidden, cl::init (500));

static llvm::cl::opt<unsigned>
HornMaxDepth("horn-max-depth", cl::Hidden,
             cl::desc ("Maximum exploration depth"),
             cl::init (UINT_MAX));

namespace seahorn
{
  char HornSolver::ID = 0;

  bool HornSolver::runOnModule (Module &M)
  {
    Stats::sset ("Result", "UNKNOWN");

    HornifyModule &hm = getAnalysis<HornifyModule> ();

    // Load the Horn clause database
    auto &db = hm.getHornClauseDB ();

    m_fp.reset (new ZFixedPoint<EZ3> (hm.getZContext ()));
    ZFixedPoint<EZ3> &fp = *m_fp;

    ZParams<EZ3> params (hm.getZContext ());
    params.set (":engine", PdrEngine);
    // -- disable slicing so that we can use cover
    params.set (":xform.slice", false);
    params.set (":use_heavy_mev", true);
    params.set (":reset_obligation_queue", true);
    params.set (":pdr.flexible_trace", FlexTrace);
    params.set (":xform.inline-linear", false);
    params.set (":xform.inline-eager", false);
    // -- disable utvpi. It is unstable.
    params.set (":pdr.utvpi", false);
    // -- disable propagate_variable_equivalences in tail_simplifier
    params.set (":xform.tail_simplifier_pve", false);
    params.set (":xform.subsumption_checker", Subsumption);
    params.set (":order_children", HornChildren ? 1U : 0U);
    params.set (":pdr.max_num_contexts", PdrContexts);
    // -- XXX the parameter is renamed to spacer.max_level in newer
    // -- XXX version of SPACER
    params.set (":pdr.max_level", HornMaxDepth);
    fp.set (params);

    db.loadZFixedPoint (fp, SkipConstraints);

    Stats::resume ("Horn");
    m_result = fp.query ();
    Stats::stop ("Horn");

    if (m_result) outs () << "sat";
    else if (!m_result) outs () << "unsat";
    else outs () << "unknown";
    outs () << "\n";

    if (m_result) Stats::sset ("Result", "FALSE");
    else if (!m_result) Stats::sset ("Result", "TRUE");

    LOG ("answer",
         if (m_result || !m_result) errs () << fp.getAnswer () << "\n";);


    if (PrintAnswer && !m_result)
    {
      HornDbModel dbModel;
      initDBModelFromFP(dbModel, db, fp);
      printInvars(M, dbModel);
    }
    else if (PrintAnswer && m_result)
      printCex ();

    if (EstimateSizeInvars)
      estimateSizeInvars(M);

    return false;
  }

  void HornSolver::getAnalysisUsage (AnalysisUsage &AU) const
  {
    AU.addRequired<HornifyModule> ();
    AU.setPreservesAll ();
  }

  void HornSolver::printCex ()
  {
    ZFixedPoint<EZ3> fp = *m_fp;
    //outs () << *fp.getCex () << "\n";

    ExprVector rules;
    fp.getCexRules (rules);
    boost::reverse (rules);
    for (Expr r : rules)
    {
      Expr src;
      Expr dst;

      if (isOpX<IMPL> (r))
      {
        dst = r->arg (1);
        r = r->arg (0);
        src = isOpX<AND> (r) ? r->arg (0) : r;
      }
      else
        dst = r;

      if (src)
      {
        if (!bind::isFapp (src)) src.reset (0);
        else src = bind::fname (bind::fname (src));
      }


      if (src) outs () << *src << " --> ";

      dst = bind::fname (bind::fname (dst));
      outs () << *dst << "\n";
    }

  }

  void HornSolver::estimateSizeInvars (Module &M)
  {
    HornifyModule &hm = getAnalysis<HornifyModule> ();
    ZFixedPoint<EZ3> fp = *m_fp;

    Expr allInvars;
    bool first = true;
    unsigned numBlocks = 0;
    for (auto &F : M)
    {
      if (F.isDeclaration ()) continue;
      for (auto &BB : F)
      {
        if (!hm.hasBbPredicate (BB)) continue;
        Expr bbPred = hm.bbPredicate (BB);
        const ExprVector &live = hm.live (BB);
        Expr invars = fp.getCoverDelta (bind::fapp (bbPred, live));
        numBlocks++;
        if (first) {
          allInvars = invars;
          first = false;
        } else {
          allInvars = mk<AND> (allInvars, invars);
        }
      }
    }
    Stats::uset ("NumOfBlocksWithInvariants", numBlocks);
    Stats::uset ("SizeOfInvariants", (allInvars ? dagSize(allInvars) : 0));
  }

  void HornSolver::printInvars (Module &M, HornDbModel &model)
  {
    for (auto &F : M) printInvars (F, model);
  }

  void HornSolver::printInvars(Function &F, HornDbModel &model)
  {
    if (F.isDeclaration ()) return;

    HornifyModule &hm = getAnalysis<HornifyModule> ();
    outs () << "Function: " << F.getName () << "\n";

    // -- not used for now
    Expr summary = hm.summaryPredicate (F);

    ZFixedPoint<EZ3> fp = *m_fp;

    for (auto &BB : F)
    {
      if (!hm.hasBbPredicate (BB)) continue;

      Expr bbPred = hm.bbPredicate (BB);

      outs () << *bind::fname (bbPred) << ":";
      const ExprVector &live = hm.live (BB);
      //Expr invars = fp.getCoverDelta (bind::fapp (bbPred, live));
      Expr invars = model.getDef(bind::fapp(bbPred, live));

      if (isOpX<AND> (invars))
      {
        outs () << "\n\t";
        for (size_t i = 0; i < invars->arity (); ++i)
          outs () << "\t" << *invars->arg (i) << "\n";
      }
      else
        outs () << " " << *invars << "\n";
    }
  }


}
