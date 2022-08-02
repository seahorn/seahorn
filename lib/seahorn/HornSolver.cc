#include "seahorn/HornSolver.hh"
#include "seahorn/Expr/ExprLlvm.hh"
#include "seahorn/Expr/ExprOpFiniteMap.hh"
#include "seahorn/HornClauseDBTransf.hh"
#include "seahorn/HornDbModel.hh"
#include "seahorn/HornifyModule.hh"

#include "seahorn/Support/Stats.hh"
#include "llvm/IR/Function.h"
#include "llvm/Support/CommandLine.h"

#include "boost/range/algorithm/reverse.hpp"

#include "seahorn/Support/SeaDebug.h"
#include <climits>

namespace seahorn {
extern bool InterProcMemFmaps;
}

using namespace llvm;

static llvm::cl::opt<std::string> ChcEngine("horn-pdr-engine",
                                            llvm::cl::desc("CHC engine to use"),
                                            cl::init("spacer"), cl::Hidden);

static llvm::cl::opt<bool>
    LocalContext("horn-solver-local-ctx", cl::init(false),
                 cl::desc("Whether to use local z3 context"));

static llvm::cl::opt<bool>
    PrintSolverStatistics("horn-solver-statistics", cl::init(false),
                          cl::desc("Whether to print statistics of spacer"));

static llvm::cl::opt<bool>
    PrintAnswer("horn-answer", cl::desc("Print Horn answer"), cl::init(false));

static llvm::cl::opt<bool>
    SimplifierPve("horn-tail-simplifier-pve",
                  cl::desc("Set fp.xform.tail_simplifier_pve"),
                  cl::init(false));

static llvm::cl::opt<bool> EstimateSizeInvars(
    "horn-estimate-size-invars",
    cl::desc("Give an estimation about the size of all inferred invariants"),
    cl::init(false));

static llvm::cl::opt<bool>
    SkipConstraints("horn-skip-constraints", cl::Hidden, cl::init(false),
                    cl::desc("Enabled when number of predicates exceeds 200"));

static llvm::cl::opt<bool>
    Subsumption("horn-subsumption", cl::Hidden, cl::init(true),
                cl::desc("Setting to false helps with cex"));

static llvm::cl::opt<bool> FlexTrace("horn-flex-trace", cl::Hidden,
                                     cl::init(false));

static llvm::cl::opt<unsigned> HornChildren("horn-solver-child-order",
                                            cl::Hidden, cl::init(2));

static llvm::cl::opt<unsigned> PdrContexts("horn-pdr-contexts", cl::Hidden,
                                           cl::init(500));

static llvm::cl::opt<bool> WeakAbs("horn-weak-abs", cl::Hidden, cl::init(false),
                                   cl::desc("Perform weak abstraction"));

static llvm::cl::opt<bool>
    GroundPobs("horn-solver-ground-pobs", cl::Hidden, cl::init(true),
               cl::desc("Ground proof obligations to ensure QF"));

static llvm::cl::opt<bool>
    UseMbqi("horn-use-mbqi", cl::Hidden, cl::init(false),
            cl::desc("Use model-based quantifier instantiation"));

static llvm::cl::opt<bool> KeepProxy("horn-keep-proxy", cl::Hidden,
                                     cl::init(false),
                                     cl::desc("Keep proxy variables"));

static llvm::cl::opt<unsigned>
    // 0: old implementation of unsat-core generation
    // 1: new implementation of IUC
    // 2: new implementation of IUC + min-cut optimization
    IUC("horn-iuc", cl::Hidden, cl::init(1));

static llvm::cl::opt<unsigned>
    // 0: simple Farkas plugin
    // 1: simple Farkas plugin from other partition
    // 2: Gaussian elimination optimization
    // 3: use additive IUC plugin
    IUCArith("horn-iuc-arith", cl::Hidden, cl::init(1));

namespace solver_detail {
enum invariant_usage_t {
  INACTIVE // add them but without using them (only debugging purposes)
  ,
  BG_ONLY // use invariants only in background
  ,
  ALWAYS // use invariants everywhere
};
}

static llvm::cl::opt<enum solver_detail::invariant_usage_t> UseInvariant(
    "horn-use-invs", llvm::cl::desc("Tell the solver how to use invariants"),
    llvm::cl::values(
        clEnumValN(solver_detail::INACTIVE, "inactive",
                   "Add invariants but without using them"),
        clEnumValN(solver_detail::BG_ONLY, "bg",
                   "Add invariants and using them only in background"),
        clEnumValN(solver_detail::ALWAYS, "always",
                   "Add invariants and use them everywhere")),
    llvm::cl::init(solver_detail::BG_ONLY));

static llvm::cl::opt<unsigned>
    HornMaxDepth("horn-max-depth", cl::Hidden,
                 cl::desc("Maximum exploration depth"), cl::init(UINT_MAX));

static llvm::cl::opt<bool>
    UseEufGen("horn-use-euf-gen", cl::Hidden, cl::init(true),
              cl::desc("Use euf generalizer for equalities"));

namespace seahorn {
extern bool InterProcMemFmaps;
}

namespace seahorn {
char HornSolver::ID = 0;

bool HornSolver::runOnModule(Module &M) {
  Stats::sset("Result", "UNKNOWN");

  HornifyModule &hm = getAnalysis<HornifyModule>();

  HornClauseDB &origdb = hm.getHornClauseDB();
  HornClauseDB tdb(origdb.getExprFactory());

  if (InterProcMemFmaps) { // rewrite finite maps
    removeFiniteMapsHornClausesTransf(origdb, tdb);
  }
  auto &db = InterProcMemFmaps ? tdb : origdb;

  if (LocalContext) {
    m_local_ctx.reset(new EZ3(hm.getExprFactory()));
    m_fp.reset(new ZFixedPoint<EZ3>(*m_local_ctx));
  } else {
    m_fp.reset(new ZFixedPoint<EZ3>(hm.getZContext()));
  }
  ZFixedPoint<EZ3> &fp = *m_fp;

  ZParams<EZ3> params(fp.getContext());
  params.set(":engine", ChcEngine);
  // -- disable slicing so that we can use cover
  params.set(":xform.slice", false);
  // params.set (":spacer.reset_obligation_queue", true);
  // params.set (":pdr.flexible_trace", FlexTrace);
  params.set(":xform.inline-linear", false);
  params.set(":xform.inline-eager", false);
  // -- disable propagate_variable_equivalences in tail_simplifier
  params.set(":xform.tail_simplifier_pve", SimplifierPve);
  params.set(":xform.subsumption_checker", Subsumption);
  params.set(":spacer.order_children", HornChildren);
  params.set(":spacer.max_num_contexts", PdrContexts);
  params.set(":spacer.elim_aux", true);
  params.set(":spacer.reach_dnf", true);
  if (PrintSolverStatistics)
    params.set("print_statistics", true);
  params.set(":spacer.use_bg_invs", UseInvariant == solver_detail::INACTIVE ||
                                        UseInvariant == solver_detail::BG_ONLY);
  params.set(":spacer.weak_abs", WeakAbs);
  params.set(":spacer.mbqi", UseMbqi);
  params.set(":spacer.iuc", IUC);
  params.set(":spacer.iuc.arith", IUCArith);
  // -- less incremental but constraints are popped after pushed in
  //    the solver
  params.set(":spacer.keep_proxy", KeepProxy);
  params.set(":spacer.ground_pobs", GroundPobs);
  params.set(":spacer.use_euf_gen", UseEufGen);
  params.set(":spacer.max_level", HornMaxDepth);
  fp.set(params);

  db.loadZFixedPoint(fp, SkipConstraints);

  if (UseInvariant == solver_detail::INACTIVE) {
    params.set(":spacer.use_bg_invs", false);
    fp.set(params);
  }

  Stats::resume("Horn");
  m_result = fp.query();
  Stats::stop("Horn");

  if (m_result)
    outs() << "sat";
  else if (!m_result)
    outs() << "unsat";
  else
    outs() << "unknown";
  outs() << "\n";

  if (m_result)
    Stats::sset("Result", "FALSE");
  else if (!m_result)
    Stats::sset("Result", "TRUE");

  LOG("answer", if (m_result || !m_result) errs() << fp.getAnswer() << "\n";);

  if (PrintAnswer && !m_result) {
    HornDbModel dbModel;
    initDBModelFromFP(dbModel, db, fp);
    printInvars(M, dbModel);
  } else if (PrintAnswer && m_result)
    printCex();

  if (EstimateSizeInvars)
    estimateSizeInvars(M);

  return false;
}

void HornSolver::getAnalysisUsage(AnalysisUsage &AU) const {
  AU.addRequired<HornifyModule>();
  AU.setPreservesAll();
}

void HornSolver::printCex() {
  ZFixedPoint<EZ3> fp = *m_fp;
  // outs () << *fp.getCex () << "\n";

  ExprVector rules;
  fp.getCexRules(rules);
  boost::reverse(rules);
  for (Expr r : rules) {
    Expr src;
    Expr dst;

    if (isOpX<IMPL>(r)) {
      dst = r->arg(1);
      r = r->arg(0);
      src = isOpX<AND>(r) ? r->arg(0) : r;
    } else
      dst = r;

    if (src) {
      if (!bind::isFapp(src))
        src.reset(0);
      else
        src = bind::fname(bind::fname(src));
    }

    if (src)
      outs() << *src << " --> ";

    dst = bind::fname(bind::fname(dst));
    outs() << *dst << "\n";
  }
}

void HornSolver::estimateSizeInvars(Module &M) {
  HornifyModule &hm = getAnalysis<HornifyModule>();
  ZFixedPoint<EZ3> fp = *m_fp;

  Expr allInvars;
  bool first = true;
  unsigned numBlocks = 0;
  for (auto &F : M) {
    if (F.isDeclaration())
      continue;
    for (auto &BB : F) {
      if (!hm.hasBbPredicate(BB))
        continue;
      Expr bbPred = hm.bbPredicate(BB);
      const ExprVector &live = hm.live(BB);
      Expr invars = fp.getCoverDelta(bind::fapp(bbPred, live));
      numBlocks++;
      if (first) {
        allInvars = invars;
        first = false;
      } else {
        allInvars = mk<AND>(allInvars, invars);
      }
    }
  }
  Stats::uset("NumOfBlocksWithInvariants", numBlocks);
  Stats::uset("SizeOfInvariants", (allInvars ? dagSize(allInvars) : 0));
}

void HornSolver::printInvars(Module &M, HornDbModel &model) {
  for (auto &F : M)
    printInvars(F, model);
}

// returns the invars if the encoding contained fmaps
static Expr processFmaps(Expr bbfapp, HornDbModel &model) {

  Expr bbPredDecl = bind::name(bbfapp);
  Expr bbPredTDecl = fmap::mkMapsDecl(bbPredDecl);

  if (bbPredDecl == bbPredTDecl)
    return model.getDef(bbfapp);

  ExprMap predDeclTMap;
  predDeclTMap[bbPredDecl] = bbPredTDecl;
  return model.getDef(rewriteFiniteMapArgs(bbfapp, predDeclTMap));
}

void HornSolver::printInvars(Function &F, HornDbModel &model) {
  if (F.isDeclaration())
    return;

  HornifyModule &hm = getAnalysis<HornifyModule>();
  outs() << "Function: " << F.getName() << "\n";

  // -- not used for now
  Expr summary = hm.summaryPredicate(F);

  ZFixedPoint<EZ3> fp = *m_fp;

  for (auto &BB : F) {
    if (!hm.hasBbPredicate(BB))
      continue;

    Expr bbPred = hm.bbPredicate(BB);

    outs() << *bind::fname(bbPred) << ":";
    const ExprVector &live = hm.live(BB);
    // Expr invars = fp.getCoverDelta (bind::fapp (bbPred, live));
    Expr bbfapp = bind::fapp(bbPred, live);
    Expr invars =
        InterProcMemFmaps ? processFmaps(bbfapp, model) : model.getDef(bbfapp);

    if (isOpX<AND>(invars)) {
      outs() << "\n";
      for (size_t i = 0; i < invars->arity(); ++i)
        outs() << "\t" << *invars->arg(i) << "\n";
    } else
      outs() << " " << *invars << "\n";
  }
}

} // namespace seahorn
