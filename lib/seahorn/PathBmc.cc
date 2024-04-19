#include "seahorn/config.h"

#ifndef HAVE_CLAM
#include "seahorn/PathBmc.hh"
/* Begin dummy implementation for PathBmcEngine if Clam is not available */
seahorn::solver::SolverResult seahorn::PathBmcEngine::solve() {
  ERR << "Path bmc engine only available if Clam is available";
  return seahorn::solver::SolverResult::UNKNOWN;
}

seahorn::PathBmcTrace seahorn::PathBmcEngine::getTrace() {
  seahorn::assertion_failed(
      "Path bmc engine only available if Clam is available", __FILE__,
      __LINE__);
}
/* End dummy implementation for PathBmcEngine if Clam is not available */
#else
#include "seahorn/Expr/ExprLlvm.hh"
#include "seahorn/Expr/ExprSimplifier.hh"
#include "seahorn/Expr/Smt/Solver.hh"
#ifdef WITH_YICES2
#include "seahorn/Expr/Smt/Yices2SolverImpl.hh"
#endif
#include "seahorn/Expr/Smt/Model.hh"
#include "seahorn/Expr/Smt/Z3SolverImpl.hh"
#include "seahorn/LoadCrab.hh"
#include "seahorn/PathBmc.hh"
#include "seahorn/PathBmcBoolAbs.hh"
#include "seahorn/PathBmcMuc.hh"
#include "seahorn/PathBmcUtil.hh"
#include "seahorn/Support/CFG.hh"
#include "seahorn/Support/SeaDebug.h"
#include "seahorn/Support/Stats.hh"
#include "seahorn/UfoOpSem.hh"

#include "seahorn/clam_CfgBuilder.hh"
#include "seahorn/clam_Clam.hh"
#include "clam/CrabDomain.hh"
#include "clam/CrabDomainParser.hh"
#include "clam/HeapAbstraction.hh"
#include "clam/SeaDsaHeapAbstraction.hh"

#include "seadsa/Global.hh"
#include "seadsa/SeaMemorySSA.hh"

#include "llvm/ADT/DenseMap.h"
#include "llvm/ADT/STLExtras.h"
#include "llvm/ADT/SmallSet.h"
#include "llvm/ADT/SmallVector.h"
#include "llvm/Analysis/CallGraph.h"
#include "llvm/Analysis/TargetLibraryInfo.h"
#include "llvm/Support/CommandLine.h"
#include "llvm/Support/ErrorHandling.h"
#include "llvm/Support/FileSystem.h"
#include "llvm/Support/Path.h"
#include "llvm/Support/raw_ostream.h"

#include <unordered_map>

/**
 * == Path Bmc engine ===
 *
 * Assume all functions have been inlined so we have only main.
 *
 * 1. Generate precise encoding (`encode`) of main using
 *    BvOpSem/BvOpSem2 semantics. The implementation should be
 *    parametric in terms of the semantics althought it hasn't been
 *    tested on BvOpSem2.
 * 2. Optionally, add crab invariants.
 * 3. Generate boolean abstraction (`addGlobalCrabInvariants`)
 * 4. For each model M (`solveBoolAbstraction`) of the boolean abstraction:
 *    4.1 Reconstruct program path from M
 *    4.2 Solve path with Crab (`solvePathWithCrab`):
 *        4.2.1 If sat then goto 4.3
 *        4.2.2 Otherwise, compute (generalized) blocking path
 *              (`encodeBoolPathFromCrabCex`) to refine
 *              (`refineBoolAbstraction`) the boolean abstraction and
 *              go to 4.
 *    4.3 Solve path with SMT solver (`solvePathWithSmt`):
 *        4.3.1 If sat then return "SAT"
 *        4.3.2 Otherwise, compute (generalized) blocking path (done by
 *              `SolvePathWithSmt`) to refine the boolean abstraction
 *              and go to 4.
 * 5. return "UNSAT"
 *
 *  The current implementation is VCGen dependent. In particular, the
 *  functions:
 *  - encodeBoolPathFromCrabCex
 *  - boolAbstraction
 *
 *  Moreover, encodeBoolPathFromCrabCex also requires knowledge
 *  about how the translation from LLVM bitcode to Crab is done.
 **/

namespace seahorn {
/// User Options to be shared with other path bmc engines
solver::SolverKind SmtSolver;
bool UseCrabGlobalInvariants;
bool UseCrabForSolvingPaths;
clam::CrabDomain::Type CrabDom;
bool LayeredCrabSolving;
path_bmc::MucMethodKind MucMethod;
unsigned PathTimeout;
unsigned MucTimeout;
std::string SmtOutDir;
} // namespace seahorn

static llvm::cl::opt<seahorn::solver::SolverKind, true>
    XSmtSolver("horn-bmc-smt-solver",
               llvm::cl::values(clEnumValN(seahorn::solver::SolverKind::Z3,
                                           "z3", "z3 SMT solver"),
                                clEnumValN(seahorn::solver::SolverKind::YICES2,
                                           "y2", "Yices2 SMT solver")),
               llvm::cl::desc("Choose SMT solver used by path-bmc"),
               llvm::cl::location(seahorn::SmtSolver),
               llvm::cl::init(seahorn::solver::SolverKind::Z3));

static llvm::cl::opt<bool, true> XUseCrabGlobalInvariants(
    "horn-bmc-crab-invariants",
    llvm::cl::desc("Load whole-program crab invariants in path-bmc"),
    llvm::cl::location(seahorn::UseCrabGlobalInvariants), llvm::cl::init(true));

static llvm::cl::opt<bool, true> XUseCrabForSolvingPaths(
    "horn-bmc-crab", llvm::cl::desc("Use of Crab to solve paths in path-bmc"),
    llvm::cl::location(seahorn::UseCrabForSolvingPaths), llvm::cl::init(false));

static llvm::cl::opt<clam::CrabDomain::Type, true, clam::CrabDomainParser>
    XCrabDom("horn-bmc-crab-dom",
             llvm::cl::desc("Crab abstract domain used in path-bmc"),
             llvm::cl::values(
                 clEnumValN(clam::CrabDomain::INTERVALS, "int",
                            "Classical interval domain (default)"),
                 clEnumValN(clam::CrabDomain::ZONES_SPLIT_DBM, "zones",
                            "Zones domain"),
                 clEnumValN(clam::CrabDomain::TERMS_INTERVALS, "term-int",
                            "Intervals with uninterpreted functions"),
                 clEnumValN(clam::CrabDomain::TERMS_ZONES, "rtz",
                            "Reduced product of term-dis-int and zones"),
                 clEnumValN(clam::CrabDomain::WRAPPED_INTERVALS, "w-int",
                            "Wrapped interval domain"),
                 clEnumValN(clam::CrabDomain::OCT, "oct", "Octagon domain"),
                 clEnumValN(clam::CrabDomain::PK, "pk",
                            "Convex Polyhedra and Linear Equalities domains")),
             llvm::cl::location(seahorn::CrabDom),
             llvm::cl::init(clam::CrabDomain::ZONES_SPLIT_DBM));

// It has only effect if UseCrabForSolvingPaths is enabled.
static llvm::cl::opt<bool, true> XLayeredCrabSolving(
    "horn-bmc-crab-layered-solving",
    llvm::cl::desc("Try only-boolean reasoning before using "
                   "--horn-bmc-crab-dom to prove path unsatisfiability"),
    llvm::cl::location(seahorn::LayeredCrabSolving), llvm::cl::init(false));

static llvm::cl::opt<enum seahorn::path_bmc::MucMethodKind, true> XMucMethod(
    "horn-bmc-muc",
    llvm::cl::desc(
        "Method used to compute minimal unsatisfiable cores in path-bmc"),
    llvm::cl::values(
        clEnumValN(seahorn::path_bmc::MucMethodKind::MUC_NONE, "none", "None"),
        clEnumValN(seahorn::path_bmc::MucMethodKind::MUC_ASSUMPTIONS, "assume",
                   "Solving with assumptions"),
        clEnumValN(seahorn::path_bmc::MucMethodKind::MUC_DELETION, "deletion",
                   "Deletion-based method"),
        clEnumValN(seahorn::path_bmc::MucMethodKind::MUC_BINARY_SEARCH,
                   "quickXplain", "QuickXplain method")),
    llvm::cl::location(seahorn::MucMethod),
    llvm::cl::init(seahorn::path_bmc::MucMethodKind::MUC_ASSUMPTIONS));

// Only if z3
static llvm::cl::opt<unsigned, true> XPathTimeout(
    "horn-bmc-path-timeout",
    llvm::cl::desc("Timeout (sec) for SMT solving a path formula in path-bmc"),
    llvm::cl::location(seahorn::PathTimeout), llvm::cl::init(1800u));

// Only if z3
static llvm::cl::opt<unsigned, true> XMucTimeout(
    "horn-bmc-muc-timeout",
    llvm::cl::desc("Timeout (sec) for SMT query during MUC in path-bmc"),
    llvm::cl::location(seahorn::MucTimeout), llvm::cl::init(5u));

static llvm::cl::opt<std::string, true> XSmtOutDir(
    "horn-bmc-smt-outdir",
    llvm::cl::desc("Directory to dump path formulas in SMT-LIB format"),
    llvm::cl::location(seahorn::SmtOutDir), llvm::cl::init(""),
    llvm::cl::value_desc("directory"));

namespace seahorn {

// To print messages with timestamps
static llvm::raw_ostream &get_os(bool show_time = false) {
  llvm::raw_ostream *result = &llvm::errs();
  if (show_time) {
    time_t now = time(0);
    struct tm tstruct;
    char buf[80];
    tstruct = *localtime(&now);
    strftime(buf, sizeof(buf), "[%Y-%m-%d.%X] ", &tstruct);
    *result << buf;
  }
  return *result;
}

void PathBmcEngine::initializeCrab() {
  // -- Set parameters for CFG
  clam::CrabBuilderParams cfg_builder_params;
  cfg_builder_params.simplify = false;
  cfg_builder_params.setPrecision(clam::CrabBuilderPrecision::MEM);
  LOG("bmc-crab-cfg", cfg_builder_params.print_cfg = true;);
  // TODO/FIXME: it should be sync with horn-bv-singleton-aliases
  cfg_builder_params.lower_singleton_aliases = true;

  // -- Build an instance of clam HeapAbstraction from ShadowMem
  const Module &M = *(m_fn->getParent());
  clam::SeaDsaHeapAbstractionParams params;
  params.is_context_sensitive = (m_sm.getDsaAnalysis().kind() == GlobalAnalysisKind::CONTEXT_SENSITIVE);
  params.precision_level = clam::CrabBuilderPrecision::MEM;  
  std::unique_ptr<clam::HeapAbstraction> heap_abs =
    std::make_unique<clam::SeaDsaHeapAbstraction>(M, m_sm.getDsaAnalysis(), params);
  m_mem_ssa = m_sm.getMemorySSA(*const_cast<Function *>(m_fn));
  assert(m_mem_ssa);

  // -- Create a CFG manager
  m_cfg_builder_man.reset(new clam::CrabBuilderManager(
      cfg_builder_params, m_tli, std::move(heap_abs)));

  
  if (UseCrabForSolvingPaths) {
    // -- Create Crab CFG for m_fn and initialize crab for solving paths
    m_crab_path_solver.reset(new clam::IntraClam(*m_fn, *m_cfg_builder_man));
  } else if(UseCrabGlobalInvariants) {
    // -- Create Crab CFG for m_fn
    m_cfg_builder_man->mkCfgBuilder(*m_fn);
  }

  // -- Run liveness analysis 
  if (clam::CfgBuilder *cfgBuilder = m_cfg_builder_man->getCfgBuilder(*m_fn)) {
    cfgBuilder->computeLiveSymbols();
  }
}

// Run whole-program crab analysis and assert those invariants into
// the solver that keeps the precise encoding.
void PathBmcEngine::addWholeProgramCrabInvariants(
    expr_invariants_map_t &invariants) {
  if (UseCrabGlobalInvariants) {
    LOG("bmc", get_os(true) << "Begin running crab analysis\n";);
    Stats::resume("BMC path-based: whole-program crab analysis");
    clam::IntraClam crab_analysis(*m_fn, *m_cfg_builder_man);

    clam::AnalysisParams params;
    params.dom = CrabDom;
    crab_analysis.analyze(params);
    Stats::stop("BMC path-based: whole-program crab analysis");
    LOG("bmc", get_os(true) << "End running crab analysis\n";);

    LOG("bmc", get_os(true) << "Begin loading of crab global invariants\n";);
    Stats::resume("BMC path-based: loading of crab global invariants");
    loadCrabInvariants(crab_analysis, invariants);
    // Assumption: the program has been fully unrolled so there is
    // exactly two cutpoint nodes (entry and exit). We use the symbolic
    // store of the exit node.
    auto &states = getStates();
    if (states.size() == 2) {
      SymStore &s = states[1];
      assertCrabInvariants(invariants, s);
    }
    Stats::stop("BMC path-based: loading of crab global invariants");
    LOG("bmc", get_os(true) << "End loading of crab invariants\n";);
  }
}

/* Load clam invariants into the out map */
void PathBmcEngine::loadCrabInvariants(
    const clam::IntraClam &crab,
    DenseMap<const BasicBlock *, ExprVector> &out) {

  auto cfgBuilder = m_cfg_builder_man->getCfgBuilder(*m_fn);
  clam::lin_cst_unordered_map<Expr> cache;
  for (const BasicBlock &bb : *m_fn) {

    // -- Get crab invariants 
    llvm::Optional<clam::clam_abstract_domain> preOpt = crab.getPre(&bb);
    if (!preOpt.hasValue()) {
      continue;
    }
    if (preOpt.getValue().is_top()) {
      continue;
    }
    clam::clam_abstract_domain pre = preOpt.getValue();

    // -- Cleanup of the crab invariants by removing dead variables.
    llvm::Optional<clam::varset_t> live_vars = cfgBuilder->getLiveSymbols(&bb);
    if (live_vars.hasValue()) {
      std::vector<clam::var_t> proj_vars(live_vars.getValue().begin(),
					 live_vars.getValue().end());
      pre.project(proj_vars);
    }

    // -- Get a conjunction of linear constraints from crab
    //    invariants.  This will lose precision if the domain is not
    //    convex or contain array/region constraints.
    clam::lin_cst_sys_t inv_csts = pre.to_linear_constraint_system();
    
    // -- Translate crab linear constraints to ExprVector
    LinConsToExpr conv(cfgBuilder, *m_fn);
    ExprVector res;
    for (auto cst : inv_csts) {
      // XXX: will convert from crab semantics to BMC semantics.
      auto it = cache.find(cst);
      Expr e;
      if (it == cache.end()) {
        if (!(cst.is_well_typed())) {
          // Crab can generate invariants where variables might have
          // different bitwidths.
          continue;
        }
        e = conv.toExpr(cst, sem(), semCtx());
      } else {
        e = it->second;
      }

      if (isOpX<FALSE>(e)) {
        res.clear();
        res.push_back(e);
        break;
      } else if (isOpX<TRUE>(e)) {
        continue;
      } else {
        cache.insert({cst, e});
        res.push_back(e);
      }
    }

    if (!res.empty()) {
      out.insert({&bb, res});
      LOG(
          "bmc-crab-load", errs() << "Global invariants at " << bb.getName() << ":\n";
          if (res.empty()) { errs() << "\ttrue\n"; } else {
            for (auto e : res) {
              errs() << "\t" << *e << "\n";
            }
          });
    }
  }
}

/* Assert the invariants as formulas in m_precise_side */
void PathBmcEngine::assertCrabInvariants(
    const expr_invariants_map_t &invariants, SymStore &s) {

  // s.print(errs());
  // Apply the symbolic store
  expr::fn_map<std::function<Expr(Expr)>> fmap([s](Expr e) { return s.at(e); });
  for (auto &kv : invariants) {
    const BasicBlock *bb = kv.first;
    const ExprVector &inv = kv.second;

    Expr sym_bb = s.at(sem().mkSymbReg(*bb, *m_semCtx));
    if (!sym_bb)
      continue;

    ExprVector eval_res;
    for (auto e : inv) {
      // XXX: we use replace instead of symbolic store eval
      // because the latter does not go through linear constraints.
      if (Expr eval_e = expr::replace(e, fmap)) {
        eval_res.push_back(eval_e);
      }
    }
    if (!eval_res.empty()) {
      // Add the invariants in m_precise_side
      m_precise_side.push_back(mk<IMPL>(sym_bb, op::boolop::land(eval_res)));
    }
  }
}

/**
 ** Helpers for path_encoding_and_solver_with_ai
 **/

/* A CFG edge is critical if it is not the only leaving its source
 * block and the only entering to the destination block.
 */
static bool isCriticalEdge(const BasicBlock *src, const BasicBlock *dst) {
  bool not_only_leaving = false;
  bool not_only_entering = false;
  for (const BasicBlock *s : succs(*src)) {
    if (s != dst) {
      not_only_leaving = true;
      break;
    }
  }
  for (const BasicBlock *p : preds(*dst)) {
    if (p != src) {
      not_only_entering = true;
      break;
    }
  }
  return (not_only_leaving && not_only_entering);
}

/*
 * encodeBoolPathFromCrabCex(cex, cex_stmts, bool_path)
 *
 * Extract/reconstruct which literals from the boolean abstraction
 * must be true to witness the spurious counterexample found by Crab.
 *
 * The reconstruction depends on the particular VCGen encoding and how
 * LLVM bitcode is translated into Crab CFGs. These are the current
 * assumptions:
 *
 *   1) Most Crab assignments "x=y" at bj are coming from PHI nodes.
 *      Given "bi: x = PHI (y, bj) (...)" VCGen encodes it into:
 *        ((bj and (bj and bi)) => x=y)
 *   2) Crab "assume(cst)" at bbi is coming from "f = ICMP cst at bb, BR f bbi,
 *      bbj", VCGen produces:
 *        ((bb and (bb and bbi)) => f)
 *
 *   3) Memory accesses must be treated carefully since Crab does not
 *      preserve memory SSA form.
 *      OLD: A binary operation or array read/write s at bb is translated by
 * VCGen to (bb => s)
 *
 *   We need to take special care if an edge is critical:
 *       - a PHI node is translated into bj and tuple(bi,bj) => x=y
 *       - a branch is translated into b and tuple(bb,bbi) => f
 */
static Expr encodeEdge(const BasicBlock &src, const BasicBlock &dst,
                       OperationalSemantics &sem, OpSemContext& semCtx,
                       std::function<Expr(Expr)> eval) {
  Expr srcE = sem.mkSymbReg(src, semCtx);
  Expr dstE = sem.mkSymbReg(dst, semCtx);
  Expr res;
  if (isCriticalEdge(&src, &dst)) {
    Expr edge = eval(path_bmc::expr_utils::mkEdge(srcE, dstE));
    res = mk<AND>(eval(srcE), edge);
  } else {
    res = mk<AND>(eval(srcE), eval(dstE));
  }
  return res;
}

static Expr encodeBasicBlock(const BasicBlock &bb,
                             OperationalSemantics &sem, OpSemContext& semCtx,
                             std::function<Expr(Expr)> eval) {
  return eval(sem.mkSymbReg(bb, semCtx));
}

// s is the Crab statement originated from PHI
static Expr encodePHI(clam::statement_t &s, const PHINode &PHI,
                      OperationalSemantics &sem, OpSemContext& semCtx,
                      std::function<Expr(Expr)> eval) {
  const BasicBlock *dst = PHI.getParent();
  const BasicBlock *src = s.get_parent()->label().get_basic_block();
  if (!src) {
    src = s.get_parent()->label().get_edge().first;
    assert(src);
  }
  if (src && dst) {
    return encodeEdge(*src, *dst, sem, semCtx, eval);
  } else {
    WARN << "encodePHI did not succeed";
    return Expr();
  }
}

static bool isMemRead(const clam::statement_t &s) {
  return s.is_arr_read() || s.is_ref_load();
}

static bool isMemWrite(const clam::statement_t &s) {
  return s.is_arr_write() || s.is_ref_store();
}

static void getMemoryDefs(const std::vector<clam::statement_t *> stmts,
                          seadsa::SeaMemorySSA &memSSA,
                          const clam::CfgBuilder &cfgBuilder,
                          SmallSet<seadsa::SeaMemoryDef *, 8> &out) {

  LOG("bmc-crab-bc", errs() << "Memory definitions={";);
  for (auto s : stmts) {
    if (isMemWrite(*s)) {
      if (const Instruction *I = cfgBuilder.getInstruction(*s)) {
        if (seadsa::SeaMemoryDef *def =
                dyn_cast<seadsa::SeaMemoryDef>(memSSA.getMemoryAccess(I))) {
          LOG("bmc-crab-bc", errs() << *def << ";";);
          out.insert(def);
        }
      }
    }
  }
  LOG("bmc-crab-bc", errs() << "}\n";);
}

// out maps each PHI node to the incoming block executed in cex.
template <class BmcTrace>
static void getExecutedPHIIncomingBlocks(
    BmcTrace &cex, seadsa::SeaMemorySSA &memSSA,
    DenseMap<const seadsa::SeaMemoryPhi *, SmallVector<unsigned, 4>> &out) {
  SmallSet<const BasicBlock *, 16> reachable_bbs;
  for (unsigned i = 0, sz = cex.size(); i < sz; ++i) {
    reachable_bbs.insert(cex.bb(i));
  }

  for (unsigned i = 0, sz = cex.size(); i < sz; ++i) {
    const BasicBlock *bb = cex.bb(i);
    for (const seadsa::SeaMemoryPhi &memPhi : memSSA.getMemoryAccesses(bb)) {
      // IMPROVE: all the memPhi should have been reachable from the
      // same incoming block
      for (unsigned j = 0; j < memPhi.getNumIncomingValues(); ++j) {
        const BasicBlock *IncBB = memPhi.getIncomingBlock(j);
        if (reachable_bbs.count(IncBB) > 0) {
          // A memory PHI can have more than one reachable incoming blocks
          // E.g., A -> B -> C and A -> C. If a memory PHI is placed
          // at C then both A and B are reachable incoming blocks.
          out[&memPhi].push_back(j);
        }
      }
    }
  }
}

// Encode the PHI nodes that connect the memory use with its
// definition. Return true iff the definition is found.
static Expr encodeUseDefChain(
    clam::statement_t &s,
    const DenseMap<const seadsa::SeaMemoryPhi *, SmallVector<unsigned, 4>>
        &memPHIInfo,
    seadsa::SeaMemorySSA &memSSA, const clam::CfgBuilder &cfgBuilder,
    const SmallSet<seadsa::SeaMemoryDef *, 8> &defs,
    OperationalSemantics &sem, OpSemContext& semCtx, std::function<Expr(Expr)> eval) {

  seadsa::SeaMemoryUse *use = nullptr;
  if (isMemRead(s)) {
    if (const Instruction *I = cfgBuilder.getInstruction(s)) {
      use = dyn_cast<seadsa::SeaMemoryUse>(memSSA.getMemoryAccess(I));
    }
  }
  if (!use) {
    WARN << "encodeUseDefChain did not succeed";
    return Expr();
  }

  LOG("bmc-crab-bc", errs()
                         << "Computing use-def chain from " << *use << "\n";);
  seadsa::SeaMemoryAccess *cur = use->getDefiningAccess();
  ExprVector res{mk<TRUE>(sem.efac())};
  while (true) {
    LOG("bmc-crab-bc", errs() << "\t" << *cur << "\n";);

    if (seadsa::SeaMemoryDef *memDef = dyn_cast<seadsa::SeaMemoryDef>(cur)) {
      if (defs.count(memDef) > 0) {
        LOG("bmc-crab-bc", errs() << "\tFinished successfully at definition "
                                  << *memDef << "\n";);
        return op::boolop::land(res);
      }
    }

    if (seadsa::SeaMemoryPhi *memPhi = dyn_cast<seadsa::SeaMemoryPhi>(cur)) {
      auto it = memPHIInfo.find(memPhi);
      if (it != memPHIInfo.end()) {
        auto reachIncomingOpIdxs = it->second;
        LOG("bmc-crab-bc", errs() << "\tThe MemoryPhi has "
                                  << reachIncomingOpIdxs.size()
                                  << " live incoming blocks\n";);
        ExprVector PhiE;
        // If there are more than one reachable incoming operand then
        // we need to encode them as a disjunction.
        seadsa::SeaMemoryAccess *phiIncMem = nullptr;
        for (unsigned incOpIdx : reachIncomingOpIdxs) {
          if (!phiIncMem) {
            phiIncMem = memPhi->getIncomingValue(incOpIdx);
          } else {
            if (phiIncMem != memPhi->getIncomingValue(incOpIdx)) {
              // TODO: we should keep chasing both regions.
              // For now, we bail out and resort to SMT.
              WARN << "encodeUseDefChain: aborted with " << *memPhi
                   << " because two incoming operands with different memory "
                      "regions\n"
                   << "\t" << *phiIncMem << "\n\t"
                   << *(memPhi->getIncomingValue(incOpIdx));
              return Expr();
            }
          }
          if (Expr incOpE = encodeEdge(*(memPhi->getIncomingBlock(incOpIdx)),
                                       *(memPhi->getBlock()), sem, semCtx, eval)) {
            PhiE.push_back(incOpE);
          } else {
            WARN << "encodeUseDefChain: failed while encoding incoming op "
                 << incOpIdx << " in " << *memPhi;
            return Expr();
          }
        }
        cur = phiIncMem;
        assert(!PhiE.empty());
        if (PhiE.size() == 1) {
          res.push_back(PhiE[0]);
        } else if (PhiE.size() == 2) {
          res.push_back(op::boolop::lor(PhiE[0], PhiE[1]));
        } else {
          res.push_back(mknary<OR>(PhiE));
        }
      } else {
        WARN << "encodeUseDefChain: does not know which incoming op to follow "
                "in "
             << *memPhi;
        return Expr();
      }
    } else {
      WARN << "encodeUseDefChain: unsupported memory instruction " << *cur;
      return Expr();
    }
  }
  return Expr();
}

template <class BmcTrace>
bool PathBmcEngine::encodeBoolPathFromCrabCex(
    BmcTrace &cex, const std::vector<clam::statement_t *> &cex_stmts,
    ExprSet &boolPath) {

  using assign_t = typename clam::cfg_ref_t::basic_block_t::assign_t;
  using bool_assign_var_t =
      typename clam::cfg_ref_t::basic_block_t::bool_assign_var_t;
  using arr_assign_t = typename clam::cfg_ref_t::basic_block_t::arr_assign_t;
  auto evalE = [this](Expr e) { return eval(e); };

  LOG("bmc-crab-bc", errs()
                         << "\nGenerating blocking path from Crab cex ...\n";);

  const clam::CfgBuilder &cfgBuilder = *m_cfg_builder_man->getCfgBuilder(*m_fn);
  SmallSet<seadsa::SeaMemoryDef *, 8> mem_defs;
  DenseMap<const seadsa::SeaMemoryPhi *, SmallVector<unsigned, 4>>
      mem_phis_exec_inc_block;

  getMemoryDefs(cex_stmts, *m_mem_ssa, cfgBuilder, mem_defs);
  getExecutedPHIIncomingBlocks(cex, *m_mem_ssa, mem_phis_exec_inc_block);

  for (auto it = cex_stmts.begin(); it != cex_stmts.end(); ++it) {
    auto s = *it;
    LOG("bmc-crab-bc", crab::outs() << *s << "\n";);
    Expr sE; // the encoding of s
    if (s->is_havoc()) {
      // do nothing
      continue;
    } else if ( // enumerate all statements so we don't miss one.
	/*integer operations*/
        s->is_bin_op() || s->is_int_cast() || s->is_select() ||
	s->is_assume() || s->is_assert() ||
	/* boolean operations */
        s->is_bool_bin_op() || s->is_bool_assign_cst() || 
        s->is_bool_assume() || s->is_bool_select() || s->is_bool_assert() ||
	/* array operations */
	s->is_arr_write() || s->is_arr_read() || s->is_arr_init() ||
	/* region and reference operations */
	s->is_region_init() || s->is_region_cast() || s->is_region_copy() ||
	s->is_ref_load() ||  s->is_ref_store() || 
	s->is_ref_make() || s->is_ref_remove() || s->is_ref_gep() ||
	s->is_ref_assume() || s->is_ref_assert()) {
      
      if (isMemRead(*s)) {
        sE = encodeUseDefChain(*s, mem_phis_exec_inc_block, *m_mem_ssa,
                               cfgBuilder, mem_defs, sem(), semCtx(), evalE);
      } else {
        if (s->get_parent()->label().is_edge()) {
          auto p = s->get_parent()->label().get_edge();
          sE = encodeEdge(*(p.first), *(p.second), sem(), semCtx(), evalE);
        } else {
          sE = encodeBasicBlock(*(s->get_parent()->label().get_basic_block()),
                                sem(), semCtx(), evalE);
        }
      }
    } else if (s->is_assign() || s->is_bool_assign_var() || s->is_arr_assign()) {
      /*
       * If there is an assignment then it might be originated from a
       * PHI node.  In that case, it's not sound just to consider the
       * block bb where the PHI node is defined but instead, we need
       * to include the edge from the PHI's incoming block to bb.
       */

      const PHINode *PHI = nullptr;
      if (s->is_assign()) {
        auto assign = static_cast<const assign_t *>(s);
        if (boost::optional<llvm::WeakVH> lhs =
                assign->lhs().name().get()) {
	  PHI = dyn_cast<PHINode>(*lhs);
        }
      } else if (s->is_bool_assign_var()) {
        auto assign = static_cast<const bool_assign_var_t *>(s);
        if (boost::optional<llvm::WeakVH> lhs =
                assign->lhs().name().get()) {
          PHI = dyn_cast<PHINode>(*lhs);
        }
      } else if (s->is_arr_assign()) {
        auto assign = static_cast<const arr_assign_t *>(s);
        if (boost::optional<llvm::WeakVH> lhs =
                assign->lhs().name().get()) {
          PHI = dyn_cast<PHINode>(*lhs);
        }
      }

      if (PHI) {
        sE = encodePHI(*s, *PHI, sem(), semCtx(), evalE);
      } else {
        assert(!s->get_parent()->label().is_edge());
        const BasicBlock *BB = s->get_parent()->label().get_basic_block();
        assert(BB);
        sE = encodeBasicBlock(*BB, sem(), semCtx(), evalE);
      }
    } else {
      crab::outs() << *s << "\n";
      ERR << "PathBmc::encodeBoolPathFromCrabCex: unsupported crab statement";
    }

    if (!sE) {
      return false;
    }

    boolPath.insert(sE);
  } // end for
  return true;
}

/*
 * Evaluate an expression using the symbolic store.
 * Needed when Crab adds blocking clauses into the boolean abstraction.
 * Assume that encode() has been executed already.
 */
Expr PathBmcEngine::eval(Expr e) {
  // XXX: since PathBmc only works with loop-free programs we should
  // have only two cutpoint nodes.
  assert(getCps().size() == 2);

  // XXX: this is the symbolic store we care about it (ensured by
  // encode()).
  auto &states = getStates();
  SymStore &s = states[1];

  Expr v = s.eval(e);
  if (v != e) {
    return v;
  }
  if (path_bmc::expr_utils::isEdge(e)) {
    // HACK: s.eval does not traverse function declarations
    auto t = path_bmc::expr_utils::getEdge(e);
    if (s.isDefined(t.first) && s.isDefined(t.second)) {
      return path_bmc::expr_utils::mkEdge(s.eval(t.first), s.eval(t.second));
    }
  }
  return nullptr;
}

/*
 * Given a sequence of basic blocks, extract the crab post-conditions
 * per block and convert it to Expr format.
 */
void PathBmcEngine::extractPostConditionsFromCrabCex(
    const std::vector<const llvm::BasicBlock *> &cex,
    const crab_invariants_map_t &postconditions, expr_invariants_map_t &out) {

  const Function &fn = *m_fn;
  ExprFactory &efac = sem().efac();

  auto get_crab_linear_constraints = [&postconditions](const BasicBlock *b) {
    auto it = postconditions.find(b);
    if (it != postconditions.end()) {
      return it->second.to_linear_constraint_system();
    } else {
      // if the block is not found then the value is assumed to be
      // bottom.
      clam::lin_cst_sys_t res(clam::lin_cst_t::get_false());
      return res;
    }
  };

  auto cfgBuilder = m_cfg_builder_man->getCfgBuilder(fn);
  for (const BasicBlock *b : cex) {
    // XXX: this will lose precision if the domain is not convex or
    // contain array constraints
    clam::lin_cst_sys_t csts = get_crab_linear_constraints(b);
    ExprVector f;

    // TODO: we can use live symbols from CfgBuilder to make more
    //       concise invariants.    
    LinConsToExpr conv(cfgBuilder, fn);
    for (auto cst : csts) {
      // XXX: Convert to Expr using Crab semantics (linear integer
      // arithmetic).
      Expr e = conv.toExpr(cst, efac);
      if (isOpX<FALSE>(e)) {
        f.clear();
        f.push_back(e);
      } else if (isOpX<TRUE>(e)) {
        continue;
      } else {
        f.push_back(e);
      }
    }
    out.insert({b, f});
  }
}

/*
   It builds a sliced Crab CFG wrt cex and performs abstract
   interpretation on it. This sliced CFG should correspond to a path
   in the original CFG.

   Return false iff the abstract interpretation of path is bottom. If
   bottom then it computes a blocking clause for that path. Otherwise,
   crab_postconditions contains the strongest postconditions
   computed by Crab. 

   Modify m_gen_path.
 */
template <class BmcTrace>
bool PathBmcEngine::solvePathWithCrab(
    BmcTrace &cex, bool compute_sp,
    crab_invariants_map_t &crab_postconditions,
    expr_invariants_map_t &expr_postconditions) {

  using namespace clam;
  std::vector<const llvm::BasicBlock *> cex_blocks;
  LOG("bmc-details-crab", errs() << "Trace=";);
  for (unsigned i = 0, sz = cex.size(); i < sz; i++) {
    cex_blocks.push_back(cex.bb(i));
    LOG("bmc-details-crab", errs() << cex.bb(i)->getName() << "  ";);
  }

  LOG("bmc-details-crab", errs() << "\n";);

  // -- crab parameters
  AnalysisParams params;
  params.dom = CrabDom;

  // -- run crab on the path:
  //    If bottom is inferred then cex_relevant_stmts is a minimal subset of
  //    statements along the path that still implies bottom.
  std::vector<clam::statement_t *> cex_relevant_stmts;

  LOG("bmc-crab", compute_sp = true;);
  bool res;
  if (compute_sp) {
    res =
        m_crab_path_solver->pathAnalyze(params, cex_blocks, LayeredCrabSolving,
                                        cex_relevant_stmts, crab_postconditions);
    // conversion from crab to Expr
    extractPostConditionsFromCrabCex(cex_blocks, crab_postconditions,
				     expr_postconditions);
                                     
  } else {
    res = m_crab_path_solver->pathAnalyze(
        params, cex_blocks, LayeredCrabSolving, cex_relevant_stmts);
  }

  if (res) {
    LOG(
        "bmc-crab", errs() << "Crab cannot prove unsat.\n"
                           << "Post-conditions computed by crab:\n";
        for (unsigned i = 0, sz = cex_blocks.size(); i < sz; ++i) {
          auto it = expr_postconditions.find(cex_blocks[i]);
          if (it != expr_postconditions.end()) {
            errs() << cex_blocks[i]->getName() << ":\n";
            for (auto e : it->second) {
              errs() << "\t" << *e << "\n";
            }
          }
        });
  } else {
    LOG(
        "bmc", get_os() << "Crab proved unsat.";
        // count the number of llvm instructions in the path
        unsigned num_stmts = 0;
        for (auto BB
             : cex_blocks) { num_stmts += BB->size(); } get_os()
        << " |minimized crab cex|=" << cex_relevant_stmts.size()
        << " |total crab cex|=" << num_stmts << ".\n";);

    LOG(
        "bmc-crab", errs() << "\nCrab cex:\n"; for (auto &s
                                                    : cex_relevant_stmts) {
          errs() << s->get_parent()->label().get_name();
          if (s->get_parent()->label().is_edge()) {
            auto e = s->get_parent()->label().get_edge();
            errs() << " (" << e.first->getName() << "," << e.second->getName()
                   << ")";
          }
          errs() << ":\n";
          crab::outs() << "\t" << *s << "\n";
        });

    // -- Extract the path from the spurious cex.
    std::set<Expr> gen_path;
    assert(m_cfg_builder_man->hasCfg(*m_fn));
    if (!encodeBoolPathFromCrabCex(cex, cex_relevant_stmts, gen_path)) {
      // By returning true we pretend the query was sat so we run
      // the SMT solver next.
      return true;
    }
    m_gen_path.clear();
    m_gen_path.assign(gen_path.begin(), gen_path.end());

#if 0
    //// DEBUGGING    
    Expr crab_bc = op::boolop::lneg(op::boolop::land(m_gen_path));
    llvm::errs() << "Blocking path using crab: " << *crab_bc << "\n";
    m_gen_path.clear();
    return true;
#endif
  }
  return res;
}

/*
  First, it builds an implicant of the precise encoding (m_precise_side)
  with respect to the model. This implicant should correspond to a
  path. Then, it checks that the implicant is unsatisfiable. If yes,
  it produces a blocking clause for that path. Otherwise, it
  produces a model.

  Modify: m_smt_path_solver, m_gen_path, and m_model.

  NOTE: Currently, blocking clauses are Boolean since the only
  abstraction we handle is Boolean.
*/
template <class BmcTrace>
solver::SolverResult PathBmcEngine::solvePathWithSmt(
    const BmcTrace &cex, const expr_invariants_map_t & /*invariants*/,
    // extra constraints inferred by
    // crab for current implicant
    const expr_invariants_map_t & /*postconditions*/) {

  const ExprVector &path_formula = cex.get_implicant_formula();
  const ExprMap &implicant_bools_map = cex.get_implicant_bools_map();

  LOG(
      "bmc-details", errs() << "PATH FORMULA:\n";
      for (Expr e
           : path_formula) { errs() << "\t" << *e << "\n"; });

  // For debugging
  // if (SmtOutDir != "") {
  //   toSmtLib(path_formula);
  // }

  /*****************************************************************
   * This check might be expensive if path_formula contains complex
   * bitvector/floating point expressions.
   * TODO: make decisions `a la` mcsat to solve faster. We will use
   * here invariants to make only those decisions which are
   * consistent with the invariants.
   *****************************************************************/
  m_smt_path_solver->reset();
  // TODO: add here postconditions to help
  for (Expr e : path_formula) {
    m_smt_path_solver->add(e);
  }

  solver::SolverResult res;
  {
    path_bmc::scopedSolver ss(*m_smt_path_solver, PathTimeout);
    res = ss.get().check();
  }
  if (res == solver::SolverResult::SAT) {
    m_model = m_smt_path_solver->get_model();
    if (SmtOutDir != "") {
      toSmtLib(path_formula, "sat");
    }
  } else {
    // Stats::resume ("BMC path-based: SMT unsat core");
    // --- Compute minimal unsat core of the path formula
    enum path_bmc::MucMethodKind muc_method = MucMethod;
    if (res == solver::SolverResult::UNSAT) {
      LOG("bmc", get_os() << "SMT proved unsat. Size of path formula="
                          << path_formula.size() << ". ");
    } else {
      LOG("bmc", get_os() << "SMT returned unknown. Size of path formula="
                          << path_formula.size() << ". ");
      Stats::count("BMC total number of unknown symbolic paths");

      muc_method = path_bmc::MucMethodKind::MUC_NONE;
      // We pretend the query is unsat to keep going but remember the
      // unknown query in m_unsolved_path_formulas.
      res = solver::SolverResult::UNSAT;
      // -- Enqueue the unknown path formula
      m_unsolved_path_formulas.push(std::make_pair(m_num_paths, path_formula));

      if (SmtOutDir != "") {
        toSmtLib(path_formula, "unknown");
      }
    }

    ExprVector unsat_core;
    switch (muc_method) {
    case path_bmc::MucMethodKind::MUC_NONE: {
      unsat_core.assign(path_formula.begin(), path_formula.end());
      break;
    }
    case path_bmc::MucMethodKind::MUC_DELETION: {
      path_bmc::MucDeletion muc(*m_smt_path_solver, MucTimeout);
      muc.run(path_formula, unsat_core);
      break;
    }
    case path_bmc::MucMethodKind::MUC_BINARY_SEARCH: {
      path_bmc::MucBinarySearch muc(*m_smt_path_solver, MucTimeout);
      muc.run(path_formula, unsat_core);
      break;
    }
    case path_bmc::MucMethodKind::MUC_ASSUMPTIONS:
    default: {
      path_bmc::MucWithAssumptions muc(*m_smt_path_solver);
      muc.run(path_formula, unsat_core);
      break;
    }
    }
    // Stats::stop ("BMC path-based: SMT unsat core");

    LOG("bmc", get_os() << "Size of unsat core=" << unsat_core.size() << "\n";);

    LOG(
        "bmc-details-uc", errs() << "unsat core=\n";
        for (auto e
             : unsat_core) { errs() << *e << "\n"; });

    // -- Refine the Boolean abstraction using the unsat core
    ExprSet gen_path;
    for (Expr e : unsat_core) {
      auto it = implicant_bools_map.find(e);
      // It's possible that an implicant has no active booleans.
      // For instance, corner cases where the whole program is a
      // single block.
      if (it != implicant_bools_map.end()) {
        gen_path.insert(it->second);
      }
    }
    m_gen_path.assign(gen_path.begin(), gen_path.end());
  }

  return res;
}

PathBmcEngine::PathBmcEngine(OperationalSemantics &sem,
                             llvm::TargetLibraryInfoWrapperPass &tli,
                             seadsa::ShadowMem &sm)
    : m_sem(sem), m_cpg(nullptr), m_fn(nullptr),
      m_ctxState(sem.efac()), m_boolean_solver(nullptr),
      m_smt_path_solver(nullptr), m_model(nullptr), m_num_paths(0), m_tli(tli),
      m_sm(sm), m_mem_ssa(nullptr), m_cfg_builder_man(nullptr),
      m_crab_path_solver(nullptr) {

  if (SmtSolver == solver::SolverKind::Z3) {
    m_boolean_solver = std::make_unique<solver::z3_solver_impl>(sem.efac());
    m_smt_path_solver = std::make_unique<solver::z3_solver_impl>(sem.efac());
    // Tuning m_aux_solver_solver's parameters
    // auto &s = static_cast<solver::z3_solver_impl&>(*m_smt_path_solver);
    // ZParams<EZ3> params(s.get_context());
    // params.set(":model_compress", false);
    // params.set(":proof", false);
    // s.get_solver().set(params);

    // z3n_set_param(":model_compress", false);
    // z3n_set_param(":proof", false);
  } else if (SmtSolver == solver::SolverKind::YICES2) {
#ifdef WITH_YICES2
    m_boolean_solver = std::make_unique<solver::yices_solver_impl>(sem.efac());
    m_smt_path_solver = std::make_unique<solver::yices_solver_impl>(sem.efac());
#else
    assertion_failed("Compile with YICES2_HOME option", __FILE__, __LINE__);
#endif
  } else {
    assertion_failed("Unsupported smt solver", __FILE__, __LINE__);
  }
}

PathBmcEngine::~PathBmcEngine() {}

void PathBmcEngine::addCutPoint(const CutPoint &cp) {
  if (m_cps.empty()) {
    m_cpg = &cp.parent();
    m_fn = cp.bb().getParent();
  }

  assert(m_cpg == &cp.parent());
  m_cps.push_back(&cp);
}

// Print a path to a SMT-LIB file (for debugging purposes)
void PathBmcEngine::toSmtLib(const ExprVector &f, std::string prefix) {
  assert(SmtOutDir != "");

  std::error_code EC;
  std::string DirName = SmtOutDir;

  // get absolute path to the directory
  SmallVector<char, 256> path;
  llvm::sys::fs::make_absolute(DirName, path);

  // create the directory
  EC = sys::fs::create_directory(path, true /*ignore if dir exists*/);
  if (EC) {
    ERR << "Cannot create directory " << DirName;
    return;
  }
  // create a file name
  std::string Filename("path_" + prefix + "_" + std::to_string(m_num_paths));
  {
    time_t now = time(0);
    struct tm tstruct;
    char buf[80];
    tstruct = *localtime(&now);
    strftime(buf, sizeof(buf), "__%Y-%m-%d.%H-%M-%S", &tstruct);
    std::string suffix(buf);
    Filename = Filename + "_" + suffix;
  }
  Filename = Filename + ".smt2";
  sys::path::append(path, Filename);
  Twine fullFilename(path);

  // create a file descriptor
  raw_fd_ostream fd(fullFilename.toStringRef(path), EC, sys::fs::OF_Text);
  if (EC) {
    ERR << "Could not open: " << Filename;
    return;
  }

  // dump the formula to the file descriptor
  m_smt_path_solver->reset();
  for (Expr e : f) {
    m_smt_path_solver->add(e);
  }
  m_smt_path_solver->to_smt_lib(fd);
  m_smt_path_solver->reset();
}

raw_ostream &PathBmcEngine::toSmtLib(raw_ostream &o) {
  encode();

  m_smt_path_solver->reset();
  for (Expr e : m_precise_side) {
    m_smt_path_solver->add(e);
  }
  m_smt_path_solver->to_smt_lib(o);
  m_smt_path_solver->reset();
  return o;
}

void PathBmcEngine::encode() {
  Stats::resume("BMC path-based: precise encoding");

  // -- only run the encoding once
  if (m_semCtx)
    return;

  assert(m_cpg);
  assert(m_fn);

  m_semCtx = m_sem.mkContext(m_ctxState, m_precise_side);
  VCGen vcgen(m_sem);

  // first state is the state in which execution starts
  m_states.push_back(m_semCtx->values());

  // -- for every pair of cut-points
  const CutPoint *prev = nullptr;
  for (const CutPoint *cp : m_cps) {
    if (prev) {
      const CpEdge *edg = m_cpg->getEdge(*prev, *cp);
      assert(edg);
      m_edges.push_back(edg);

      // generate vc for current edge
      vcgen.genVcForCpEdge(*m_semCtx, *edg);
      // store a copy of the state at the end of execution
      m_states.push_back(m_semCtx->values());
    }
    prev = cp;
  }

  Stats::stop("BMC path-based: precise encoding");
}

void PathBmcEngine::solveBoolAbstraction() {
  Stats::resume("BMC path-based: enumeration path solver");
  m_result = m_boolean_solver->check();
  Stats::stop("BMC path-based: enumeration path solver");
}

solver::SolverResult PathBmcEngine::solve() {
  LOG("bmc", get_os(true) << "Starting path-based BMC \n";);

  // -- Precise encoding
  LOG("bmc", get_os(true) << "Begin precise encoding\n";);
  encode();
  LOG("bmc", get_os(true) << "End precise encoding\n";);

  // -- Initialize Crab and assert global invariants to refine the
  // -- precise encoding
  initializeCrab();
  expr_invariants_map_t invariants /*currently unused*/;
  addWholeProgramCrabInvariants(invariants);

  LOG(
      "bmc-details", for (Expr v
                          : m_precise_side) { errs() << "\t" << *v << "\n"; });

  // -- Boolean abstraction
  LOG("bmc", get_os(true) << "Begin boolean abstraction\n";);
  Stats::resume("BMC path-based: initial boolean abstraction");
  ExprVector abs_side;
  path_bmc::boolAbstraction(m_precise_side, abs_side);
  // XXX: we use m_boolean_solver for keeping the abstraction.
  for (Expr v : abs_side) {
    LOG("bmc-details", errs() << "\t" << *v << "\n";);
    m_boolean_solver->add(v);
  }
  Stats::stop("BMC path-based: initial boolean abstraction");
  LOG("bmc", get_os(true) << "End boolean abstraction\n";);

  /**
   * Main loop
   *
   * Use boolean abstraction to enumerate paths. Each time a path is
   * unsat, blocking clauses are added to avoid exploring the same
   * path.
   **/
  while (true) {
    solveBoolAbstraction();

    // keep going while we can generate a path from the boolean
    // abstraction
    if (m_result != solver::SolverResult::SAT) {
      break;
    }
    ++m_num_paths;
    Stats::count("BMC total number of symbolic paths");

    LOG("bmc", get_os(true) << m_num_paths << ": ");
    Stats::resume("BMC path-based: get model");
    solver::Solver::model_ref model = m_boolean_solver->get_model();
    Stats::stop("BMC path-based: get model");

    LOG("bmc-details", errs() << "Model " << m_num_paths << " found: \n"
                              << *model << "\n";);

    Stats::resume("BMC path-based: create a cex");
    PathBmcTrace cex(*this, model);
    Stats::stop("BMC path-based: create a cex");

    expr_invariants_map_t expr_postconditions;
    if (UseCrabForSolvingPaths) {
      crab_invariants_map_t crab_postconditions /*unused*/;
      bool compute_sp = false;
      Stats::resume(
          "BMC path-based: solving path + generalized blocking path with Crab");
      bool res = solvePathWithCrab(cex, compute_sp,
                                   crab_postconditions, expr_postconditions);
      Stats::stop(
          "BMC path-based: solving path + generalized blocking path with Crab");

      LOG(
          "bmc-ai", if (!expr_postconditions.empty()) {
            errs() << "\nPath constraints (post-conditions) inferred by Crab\n";
            for (auto &kv : expr_postconditions) {
              errs() << "\t" << kv.first->getName() << ": ";
              if (kv.second.empty()) {
                errs() << "true\n";
              } else {
                errs() << "{";
                for (auto e : kv.second) {
                  errs() << *e << ";";
                }
                errs() << "}\n";
              }
            }
          });

      if (!res) {
        bool ok = refineBoolAbstraction();
        if (ok) {
          Stats::count("BMC number symbolic paths discharged by Crab");
          continue;
        } else {
          ERR << "Path-based BMC added the same blocking path again";
          m_result = solver::SolverResult::UNKNOWN;
          return m_result;
        }
      }
    }

    Stats::resume(
        "BMC path-based: solving path + generalized blocking path with SMT");
    // XXX: the semantics of invariants and expr_postconditions (e.g.,
    // linear integer arithmetic) might differ from the semantics used
    // by the smt (e.g., bitvectors).
    solver::SolverResult res =
        solvePathWithSmt(cex, invariants, expr_postconditions /*unused*/);
    Stats::stop(
        "BMC path-based: solving path + generalized blocking path with SMT");
    if (res == solver::SolverResult::SAT) {
      if (UseCrabForSolvingPaths) {
        // Temporary: for profiling crab
        crab::CrabStats::PrintBrunch(crab::outs());
      }
      m_result = res;
      return res;
    } else {
      bool ok = refineBoolAbstraction();
      if (!ok) {
        ERR << "Path-based BMC added the same blocking path again";
        m_result = solver::SolverResult::UNKNOWN;
        return m_result;
      }
      Stats::count("BMC number symbolic paths discharged by SMT");
    }
  }

  if (!m_unsolved_path_formulas.empty()) {
    m_result = solver::SolverResult::UNKNOWN;

    LOG("bmc",
        get_os()
            << "Checking again unsolved paths with increasing timeout ...\n");
    // XXX: can be user parameter
    const unsigned timeout_delta = 10; // (seconds)
    std::unordered_map<unsigned, unsigned> timeout_map;
    while (!m_unsolved_path_formulas.empty()) {
      auto kv = m_unsolved_path_formulas.front();
      m_unsolved_path_formulas.pop();

      m_smt_path_solver->reset();
      for (Expr e : kv.second) {
        m_smt_path_solver->add(e);
      }

      unsigned timeout;
      auto it = timeout_map.find(kv.first);
      if (it == timeout_map.end()) {
        timeout_map.insert(
            std::make_pair(kv.first, PathTimeout + timeout_delta));
        timeout = PathTimeout + timeout_delta;
      } else {
        timeout = it->second + timeout_delta;
        it->second = timeout;
      }

      solver::SolverResult res;
      {
        path_bmc::scopedSolver ss(*m_smt_path_solver, timeout);
        res = ss.get().check();
      }
      if (res == solver::SolverResult::SAT) {
        m_model = m_smt_path_solver->get_model();
        if (SmtOutDir != "") {
          toSmtLib(kv.second, "sat");
        }
        LOG("bmc", get_os(true) << "Path " << kv.first << " proved sat!\n";);
        m_result = solver::SolverResult::SAT;
        return m_result;
      } else if (res == solver::SolverResult::UNSAT) {
        LOG("bmc", get_os(true) << "Path " << kv.first << " proved unsat!\n";);
      } else {
        LOG("bmc", get_os(true) << "Path " << kv.first
                                << " cannot be proved unsat with timeout="
                                << timeout << "\n";);
        // put it back in the queue and try next time with a bigger timeout
        m_unsolved_path_formulas.push(kv);
      }
    }
    // If we reach this point we were able to discharge all the paths!
    Stats::uset("BMC total number of unknown symbolic paths", 0);
    m_result = solver::SolverResult::UNSAT;
  }

  if (m_num_paths == 0) {
    WARN << "Boolean abstraction is already false";
  }

  if (UseCrabForSolvingPaths) {
    // Temporary: for profiling crab
    crab::CrabStats::PrintBrunch(crab::outs());
  }

  return m_result;
}

// The (generalized) path to be excluded is already stored in m_gen_path.
bool PathBmcEngine::refineBoolAbstraction() {
  Stats::resume("BMC path-based: adding blocking clauses");

  // -- Refine the Boolean abstraction
  Expr bc = mk<FALSE>(sem().efac());
  if (m_gen_path.empty()) {
    WARN << "No path condition generated. Trivially unsat ...";
  } else {
    bc = op::boolop::lneg(op::boolop::land(m_gen_path));
  }
  LOG("bmc-details-bc",
      errs() << "Added blocking clause to refine Boolean abstraction: " << *bc
             << "\n";);

  m_boolean_solver->add(bc);
  auto res = m_blocking_clauses.insert(bc);
  bool ok = res.second;

  Stats::stop("BMC path-based: adding blocking clauses");
  return ok;
}

PathBmcTrace PathBmcEngine::getTrace() {
  assert((bool)m_result);
  PathBmcTrace cex(*this, m_model);
  return cex;
}

} // namespace seahorn
#endif
