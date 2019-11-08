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

#include "sea_dsa/AllocWrapInfo.hh"

#include "clam/AbstractDomain.hh"
#include "clam/CfgBuilder.hh"
#include "clam/Clam.hh"
#include "clam/HeapAbstraction.hh"
#include "clam/SeaDsaHeapAbstraction.hh"

#include "llvm/ADT/STLExtras.h"
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
 * 1. Generate precise encoding of main using BvOpSem semantics. The
 *    implementation should be parametric in terms of the semantics.
 * 2. Optionally, add crab invariants
 * 3. Generate boolean abstraction
 * 4. For each model M of the boolean abstraction:
 *    4.1 Reconstruct program path from M
 *    4.2 Solve path with Crab:
 *        4.2.1 If sat then goto 4.3
 *        4.2.2 Otherwise, compute blocking clause to refine the
 *              boolean abstraction and go to 4.
 *    4.3 Solve path with SMT solver:
 *        4.3.1 If sat then return "SAT"
 *        4.3.2 Otherwise, compute blocking clause to refine the boolean
 *              abstraction and go to 4.
 * 5. return "UNSAT" 
 * 
 *  The current implementation is VCGen dependent. In particular, the
 *  functions:
 *  - gen_path_cond_from_ai_cex
 *  - bool_abstraction
 * 
 *  Moreover, gen_path_cond_from_ai_cex also requires knowledge
 *  about how the translation from LLVM bitcode to Crab is done.
 **/

static llvm::cl::opt<seahorn::solver::SolverKind>
    SmtSolver("horn-bmc-smt-solver",
              llvm::cl::values(clEnumValN(seahorn::solver::SolverKind::Z3, "z3",
                                          "z3 SMT solver"),
                               clEnumValN(seahorn::solver::SolverKind::YICES2,
                                          "yices2", "Yices2 SMT solver")),
              llvm::cl::desc("Choose SMT solver used for the Path Bmc engine"),
              llvm::cl::init(seahorn::solver::SolverKind::Z3));

static llvm::cl::opt<bool> UseCrabGlobalInvariants(
    "horn-bmc-crab-invariants",
    llvm::cl::desc("Load crab invariants into the Path Bmc engine"),
    llvm::cl::init(true));

static llvm::cl::opt<bool> UseCrabForSolvingPaths(
    "horn-bmc-crab",
    llvm::cl::desc("Use of Crab to solve paths in Path Bmc engine"),
    llvm::cl::init(false));

static llvm::cl::opt<clam::CrabDomain> CrabDom(
    "horn-bmc-crab-dom",
    llvm::cl::desc("Crab Domain used by the Path Bmc engine"),
    llvm::cl::values(clEnumValN(clam::INTERVALS, "int",
                                "Classical interval domain (default)"),
                     clEnumValN(clam::ZONES_SPLIT_DBM, "zones",
                                "Zones domain."),
                     clEnumValN(clam::TERMS_INTERVALS, "term-int",
                                "Intervals with uninterpreted functions."),
                     clEnumValN(clam::TERMS_ZONES, "rtz",
                                "Reduced product of term-dis-int and zones."),
                     clEnumValN(clam::WRAPPED_INTERVALS, "w-int",
                                "Wrapped interval domain")),
    llvm::cl::init(clam::ZONES_SPLIT_DBM));

// It has only effect if UseCrabForSolvingPaths is enabled.
static llvm::cl::opt<bool> LayeredCrabSolving(
    "horn-bmc-crab-layered-solving",
    llvm::cl::desc("Try only-boolean reasoning before using "
                   "--horn-bmc-crab-dom to prove path unsatisfiability"),
    llvm::cl::init(false));

static llvm::cl::opt<enum seahorn::path_bmc::MucMethodKind> MucMethod(
    "horn-bmc-muc",
    llvm::cl::desc("Method used to compute minimal unsatisfiable cores in Path "
                   "Bmc engine"),
    llvm::cl::values(
        clEnumValN(seahorn::path_bmc::MucMethodKind::MUC_NONE, "none", "None"),
        clEnumValN(seahorn::path_bmc::MucMethodKind::MUC_ASSUMPTIONS, "assume",
                   "Solving with assumptions"),
        clEnumValN(seahorn::path_bmc::MucMethodKind::MUC_DELETION, "deletion",
                   "Deletion-based method"),
        clEnumValN(seahorn::path_bmc::MucMethodKind::MUC_BINARY_SEARCH,
                   "quickXplain", "QuickXplain method")),
    llvm::cl::init(seahorn::path_bmc::MucMethodKind::MUC_ASSUMPTIONS));

static llvm::cl::opt<unsigned> PathTimeout(
    "horn-bmc-path-timeout",
    llvm::cl::desc(
        "Timeout (sec) for SMT solving a path formula in Path Bmc engine"),
    llvm::cl::init(1800u));

static llvm::cl::opt<unsigned> MucTimeout(
    "horn-bmc-muc-timeout",
    llvm::cl::desc("Timeout (sec) for SMT query during MUC in Path Bmc engine"),
    llvm::cl::init(5u));

static llvm::cl::opt<std::string> SmtOutDir(
    "horn-bmc-smt-outdir",
    llvm::cl::desc("Directory to dump path formulas in SMT-LIB format"),
    llvm::cl::init(""), llvm::cl::value_desc("directory"));

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

/* Load clam invariants into the out map */
void PathBmcEngine::load_invariants(
    const clam::IntraClam &crab,
    DenseMap<const BasicBlock *, ExprVector> &out) {

  clam::lin_cst_unordered_map<Expr> cache;
  for (const BasicBlock &bb : *m_fn) {

    // -- Get invariants from crab as crab linear constraints
    auto pre = crab.get_pre(&bb);
    if (!pre)
      continue;
    clam::lin_cst_sys_t inv_csts = pre->to_linear_constraints();
    if (inv_csts.is_true())
      continue;

    // -- Translate crab linear constraints to ExprVector
    const ExprVector &live = m_ls->live(&bb);
    LinConsToExpr conv(*m_mem, *m_fn, live);

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
        e = conv.toExpr(cst, sem());
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
      LOG("bmc-ai", errs() << "Global invariants at " << bb.getName() << ":\n";
          if (res.empty()) { errs() << "\ttrue\n"; } else {
            for (auto e : res) {
              errs() << "\t" << *e << "\n";
            }
          });
    }
  }
}

/* Assert the invariants as formulas in m_precise_side */
void PathBmcEngine::assert_invariants(const expr_invariants_map_t &invariants,
                                      SymStore &s) {

  // s.print(errs());
  // Apply the symbolic store
  expr::fn_map<std::function<Expr(Expr)>> fmap([s](Expr e) { return s.at(e); });
  for (auto &kv : invariants) {
    const BasicBlock *bb = kv.first;
    const ExprVector &inv = kv.second;

    Expr sym_bb = s.at(sem().symb(*bb));
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
 * Extract which boolean literals from the boolean abstraction must be
 * true to witness the spurious counterexample found by Crab.
 *
 * The extraction depends on the particular VCGen encoding and how
 * LLVM bitcode is translated into Crab CFGs. These are the current
 * assumptions:
 *
 *   1) A binary operation or array read/write s at bb is translated by VCGen 
 *      to (bb => s)
 *   2) Most Crab assignments "x=y" at bj are coming from PHI nodes.
 *      Given "bi: x = PHI (y, bj) (...)" VCGen encodes it into:
 *        ((bj and (bj and bi)) => x=y)
 *   3) Crab "assume(cst)" at bbi is coming from "f = ICMP cst at bb, BR f bbi,
 *      bbj", VCGen produces:
 *        ((bb and (bb and bbi)) => f)
 * 
 *   We need to take special care if an edge is critical:
 *       - a PHI node is translated into bj and tuple(bi,bj) => x=y
 *       - a branch is translated into b and tuple(bb,bbi) => f
 */
bool PathBmcEngine::gen_path_cond_from_ai_cex(
    PathBmcTrace &cex,    					      
    const std::vector<crab_statement_t> &cex_stmts,
    ExprSet /*std::set<Expr, lessExpr>*/ &path_cond) {

  LOG("bmc-crab-blocking-clause",
      errs() << "\nGenerating blocking clause from Crab cex ...\n";);

  const clam::CfgBuilder& cfg_builder = *m_cfg_builder_man->get_cfg_builder(*m_fn);  
  for (auto it = cex_stmts.begin(); it != cex_stmts.end(); ++it) {
    auto s = *it;
    LOG("bmc-crab-blocking-clause", crab::outs() << *s.m_s << "\n";);
    if (s.m_s->is_havoc()) {
      // The only reason a havoc statement is relevant is if we have something
      // like x:=*; assume(cond(x)); assert(cond(x)) Therefore, we can skip
      // it.
      continue;
    } else if ( // enumerate all statements here so that we can know if we
                // miss one
        s.m_s->is_bin_op() || s.m_s->is_int_cast() || s.m_s->is_select() ||
        s.m_s->is_bool_bin_op() || s.m_s->is_bool_assign_cst() ||
	s.m_s->is_assume() || s.m_s->is_bool_assume() ||
	// array writes
	s.m_s->is_arr_write() || 	
	// array reads
	s.m_s->is_arr_read() || 
        // array initializations are not coming from branches
        s.m_s->is_arr_init()) {
      if (s.m_parent.is_edge()) {
        auto p = s.m_parent.get_edge();
        Expr src = sem().symb(*p.first);
        Expr dst = sem().symb(*p.second);

        Expr edge;
        if (isCriticalEdge(p.first, p.second)) {
          edge = path_bmc::expr_utils::mkEdge(src, dst);
          LOG("bmc-crab-blocking-clause",
              errs() << "\tCritical edge for branch between "
                     << p.first->getName() << " and " << p.second->getName()
                     << ": " << *edge << "\n";);
          path_cond.insert(eval(src));
        } else {
          edge = mk<AND>(src, dst);
          LOG("bmc-crab-blocking-clause",
              errs() << "\tNon-critical edge for branch between "
                     << p.first->getName() << " and " << p.second->getName()
                     << ": " << *edge << "\n";);
        }
        path_cond.insert(eval(edge));
      } else {
        const BasicBlock *BB = s.m_parent.get_basic_block();
        path_cond.insert(eval(sem().symb(*BB)));
        LOG("bmc-crab-blocking-clause", errs()
                                            << "\tbasic block " << BB->getName()
	                                    << ": " << *(sem().symb(*BB)) << "\n";);
      }
      continue;
    } else if (s.m_s->is_assign() || s.m_s->is_bool_assign_var() ||
	       s.m_s->is_arr_assign()) {
      /* 
       * If there is an assignment then it might be originated from a
       * PHI node.  In that case, it's not sound just to consider the
       * block bb where the PHI node is defined but instead, we need
       * to include the edge from the PHI's incoming block to bb.
       */

      // To record the edge
      const BasicBlock *src_BB = nullptr;
      const BasicBlock *dst_BB = nullptr;
      
      if (s.m_s->is_assign()) {
        typedef typename clam::cfg_ref_t::basic_block_t::assign_t assign_t;
        auto assign = static_cast<const assign_t *>(s.m_s);
        if (boost::optional<const llvm::Value *> lhs =
                assign->lhs().name().get()) {
	  // The crab assignment is in the incoming block of PHI
          if (const PHINode* PHI = dyn_cast<PHINode>(*lhs)) {
	    src_BB = s.m_parent.get_basic_block();
	    if (!src_BB) {
	      src_BB = s.m_parent.get_edge().first;
	      assert(src_BB);
	    }
	    dst_BB = PHI->getParent();
	  }
        }
      } else if (s.m_s->is_bool_assign_var()) {
	typedef typename clam::cfg_ref_t::basic_block_t::bool_assign_var_t
	  bool_assign_var_t;
	auto assign = static_cast<const bool_assign_var_t *>(s.m_s);
	if (boost::optional<const llvm::Value *> lhs =
	    assign->lhs().name().get()) {
          if (const PHINode* PHI = dyn_cast<PHINode>(*lhs)) {
	    // The crab assignment is in the incoming block of PHI
	    src_BB = s.m_parent.get_basic_block();
	    if (!src_BB) {
	      src_BB = s.m_parent.get_edge().first;
	      assert(src_BB);
	    }
	    dst_BB = PHI->getParent();
	  }
	}
      } else if (s.m_s->is_arr_assign()) {
	if (const PHINode *PHI = dyn_cast<PHINode>(cfg_builder.get_instruction(*s.m_s))) {
	  // The crab array assignment is in the incoming block of PHI
	  src_BB = s.m_parent.get_basic_block();
	  if (!src_BB) {
	    src_BB = s.m_parent.get_edge().first;
	    assert(src_BB);
	  }
	  dst_BB = PHI->getParent();
	}
      }

      if (src_BB && dst_BB) {
	// XXX assignments originated from PHI nodes
        Expr src = sem().symb(*src_BB);
        Expr dst = sem().symb(*dst_BB);
        Expr edge;
        if (isCriticalEdge(src_BB, dst_BB)) {
          edge = path_bmc::expr_utils::mkEdge(src, dst);
          LOG("bmc-crab-blocking-clause",
              errs() << "\tCritical edge for PHI Node between "
                     << src_BB->getName() << " and " << dst_BB->getName() << ": "
                     << *edge << "\n";);
          path_cond.insert(eval(src));
        } else {
          edge = mk<AND>(src, dst);
          LOG("bmc-crab-blocking-clause",
              errs() << "\tNon-critical edge for PHI Node between "
                     << src_BB->getName() << " and " << dst_BB->getName() << ": "
                     << *edge << "\n";);
        }
        path_cond.insert(eval(edge));
        continue;
      } else {
        // XXX assignment not originated from a PHI node
        assert(!s.m_parent.is_edge());
        const BasicBlock *BB = s.m_parent.get_basic_block();
        assert(BB);
        path_cond.insert(eval(sem().symb(*BB)));
        LOG("bmc-crab-blocking-clause", errs() << "\tbasic block for assignment "
                                               << BB->getName()
	                                       << ": " << *(sem().symb(*BB)) << "\n";);
        continue;
      }
    }
    
    // sanity check: this should not happen.
    // crab::outs() << *s.m_s << "\n";
    ERR << "PathBmc::gen_path_cond_from_cex: unsupported crab statement";
    return false;
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
  SymStore&s = states[1]; 

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
 * Given a sequence of basic blocks, extract the crab invariants per
 * block and convert it to Expr format.
 */
void PathBmcEngine::extract_post_conditions_from_ai_cex(
    const std::vector<const llvm::BasicBlock *> &cex,
    const crab_invariants_map_t &invariants,
    expr_invariants_map_t &out) {
  
  const LiveSymbols &ls = *m_ls;
  clam::HeapAbstraction &heap_abs = *m_mem;
  const Function &fn = *m_fn;
  ExprFactory &efac = sem().efac();
  
  auto get_crab_linear_constraints = [&invariants](const BasicBlock *b) {
    auto it = invariants.find(b);
    if (it != invariants.end()) {
      return it->second->to_linear_constraints();
    } else {
      // if the block is not found then the value is assumed to be
      // bottom.
      clam::lin_cst_sys_t res(clam::lin_cst_t::get_false());
      return res;
    }
  };

  for (const BasicBlock *b : cex) {
    const ExprVector &live = ls.live(b);
    // XXX: this will lose precision if the domain is not convex.
    clam::lin_cst_sys_t csts = get_crab_linear_constraints(b);
    ExprVector f;
    LinConsToExpr conv(heap_abs, fn, live);
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

   Return false iff the abstract interpretation of path is
   bottom. If bottom then it computes a blocking clause for that
   path.

   Modify m_path_cond.
 */
bool PathBmcEngine::path_encoding_and_solve_with_ai(
      PathBmcTrace &cex, expr_invariants_map_t &path_constraints) {
  
  using namespace clam;
  std::vector<const llvm::BasicBlock *> cex_blocks;
  LOG("bmc-details", errs() << "Trace=";);
  for (unsigned i = 0, sz = cex.size(); i < sz; i++) {
    cex_blocks.push_back(cex.bb(i));
    LOG("bmc-details", errs() << cex.bb(i)->getName() << "  ";);
  }
  
  LOG("bmc-details", errs() << "\n";);

  // -- crab parameters
  AnalysisParams params;
  params.dom = CrabDom;

  // -- run crab on the path:
  //    If bottom is inferred then cex_relevant_stmts is a minimal subset of
  //    statements along the path that still implies bottom.
  std::vector<crab_statement_t> cex_relevant_stmts;

  bool compute_path_constraints = false;
  LOG("bmc-crab", compute_path_constraints = true;);
  bool res;
  // currently enabled only for debugging because path_constraints is
  // unused.
  if (compute_path_constraints) { 
    // crab_invariants contains the forward invariants for the cex:
    // one abstract state per cex's block
    crab_invariants_map_t crab_invariants;
    res =
        m_crab_path_solver->path_analyze(params, cex_blocks, LayeredCrabSolving,
                                         cex_relevant_stmts, crab_invariants);
    // conversion from crab to Expr
    extract_post_conditions_from_ai_cex(cex_blocks, crab_invariants,
					path_constraints);
  } else {
    res = m_crab_path_solver->path_analyze(
        params, cex_blocks, LayeredCrabSolving, cex_relevant_stmts);
  }

  if (res) {
    LOG("bmc-crab",
	errs() << "Crab cannot prove unsat.\n"
	       << "Post-conditions computed by crab:\n";
	for (unsigned i=0,sz=cex_blocks.size();i<sz;++i) {
	  auto it = path_constraints.find(cex_blocks[i]);
	  if (it != path_constraints.end()) {
	    errs() << cex_blocks[i]->getName() << ":\n";
	    for (auto e: it->second) {
	      errs() << "\t" << *e << "\n";	    
	    }
	  }
	});
  } else  {
    LOG("bmc", get_os() << "Crab proved unsat.";
        // count the number of llvm instructions in the path
        unsigned num_stmts = 0;
        for (auto BB
             : cex_blocks) { num_stmts += BB->size(); } get_os()
        << " #Relevant statements " << cex_relevant_stmts.size() << "/"
        << num_stmts << ".\n";);

    LOG("bmc-crab", errs() << "\nRelevant Crab statements:\n";
        for (auto &s
             : cex_relevant_stmts) {
          errs() << s.m_parent.get_name();
          if (s.m_parent.is_edge()) {
            auto e = s.m_parent.get_edge();
            errs() << " (" << e.first->getName() << "," << e.second->getName()
                   << ")";
          }
          errs() << ":\n";
          crab::outs() << "\t" << *(s.m_s) << "\n";
        });

    // -- Extract the path condition from the spurious cex.
    std::set<Expr> path_cond;
    assert(m_cfg_builder_man->has_cfg(*m_fn));
    if (!gen_path_cond_from_ai_cex(cex, cex_relevant_stmts, path_cond)) {
      // By returning true we pretend the query was sat so we run
      // the SMT solver next.
      return true;
    }
    m_path_cond.clear();
    m_path_cond.assign(path_cond.begin(), path_cond.end());

    #if 0
    //// DEBUGGING    
    Expr crab_bc = op::boolop::lneg(op::boolop::land(m_path_cond));
    llvm::errs() << "Blocking clause using crab: " << *crab_bc << "\n";
    m_path_cond.clear();
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

  Modify: m_smt_path_solver, m_path_cond, and m_model.

  NOTE: Currently, blocking clauses are Boolean since the only
  abstraction we handle is Boolean.
*/
solver::SolverResult PathBmcEngine::path_encoding_and_solve_with_smt(
    const PathBmcTrace &cex, const expr_invariants_map_t & /*invariants*/,
    // extra constraints inferred by
    // crab for current implicant
    const expr_invariants_map_t & /*path_constraints*/) {

  const ExprVector &path_formula = cex.get_implicant_formula();
  const ExprMap &path_cond_map = cex.get_implicant_bools_map();

  LOG("bmc-details", errs() << "PATH FORMULA:\n";
      for (Expr e
           : path_formula) { errs() << "\t" << *e << "\n"; });

  // For debugging
  // if (SmtOutDir != "") {
  //   to_smt_lib(path_formula);
  // }

  /*****************************************************************
   * This check might be expensive if path_formula contains complex
   * bitvector/floating point expressions.
   * TODO: make decisions `a la` mcsat to solve faster. We will use
   * here invariants to make only those decisions which are
   * consistent with the invariants.
   *****************************************************************/
  m_smt_path_solver->reset();
  // TODO: add here path_constraints to help
  for (Expr e : path_formula) {
    m_smt_path_solver->add(e);
  }

  solver::SolverResult res;
  {
    path_bmc::scoped_solver ss(*m_smt_path_solver, PathTimeout);
    res = ss.get().check();
  }
  if (res == solver::SolverResult::SAT) {
    m_model = m_smt_path_solver->get_model();
    if (SmtOutDir != "") {
      to_smt_lib(path_formula, "sat");
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
        to_smt_lib(path_formula, "unknown");
      }
    }

    ExprVector unsat_core;
    switch (muc_method) {
    case path_bmc::MucMethodKind::MUC_NONE: {
      unsat_core.assign(path_formula.begin(), path_formula.end());
      break;
    }
    case path_bmc::MucMethodKind::MUC_DELETION: {
      path_bmc::deletion_muc muc(*m_smt_path_solver, MucTimeout);
      muc.run(path_formula, unsat_core);
      break;
    }
    case path_bmc::MucMethodKind::MUC_BINARY_SEARCH: {
      path_bmc::binary_search_muc muc(*m_smt_path_solver, MucTimeout);
      muc.run(path_formula, unsat_core);
      break;
    }
    case path_bmc::MucMethodKind::MUC_ASSUMPTIONS:
    default: {
      path_bmc::muc_with_assumptions muc(*m_smt_path_solver);
      muc.run(path_formula, unsat_core);
      break;
    }
    }
    // Stats::stop ("BMC path-based: SMT unsat core");

    LOG("bmc", get_os() << "Size of unsat core=" << unsat_core.size() << "\n";);
    
    LOG("bmc-details", 
	errs() << "unsat core=\n";
	for (auto e: unsat_core) {
	  errs () << *e << "\n";
	});
    
    // Stats::resume ("BMC path-based: blocking clause");
    // -- Refine the Boolean abstraction using the unsat core
    ExprSet path_cond_set;
    for (Expr e : unsat_core) {
      auto it = path_cond_map.find(e);
      // It's possible that an implicant has no active booleans.
      // For instance, corner cases where the whole program is a
      // single block.
      if (it != path_cond_map.end()) {
        path_cond_set.insert(it->second);
      }
    }
    m_path_cond.assign(path_cond_set.begin(), path_cond_set.end());
    // Stats::stop ("BMC path-based: blocking clause");
  }

  return res;
}

PathBmcEngine::PathBmcEngine(LegacyOperationalSemantics &sem,
                             const llvm::DataLayout &dl,
                             const llvm::TargetLibraryInfo &tli,
                             llvm::CallGraph &cg, sea_dsa::AllocWrapInfo &awi)
    : m_sem(sem), m_cpg(nullptr), m_fn(nullptr), m_ls(nullptr),
      m_ctxState(sem.efac()), m_boolean_solver(nullptr),
      m_smt_path_solver(nullptr), m_model(nullptr), m_num_paths(0), m_dl(dl),
      m_tli(tli), m_cg(cg), m_awi(awi),
      m_cfg_builder_man(nullptr), m_mem(nullptr), m_crab_path_solver(nullptr) {

  if (SmtSolver == solver::SolverKind::Z3) {
    m_boolean_solver = llvm::make_unique<solver::z3_solver_impl>(sem.efac());
    m_smt_path_solver = llvm::make_unique<solver::z3_solver_impl>(sem.efac());
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
    m_boolean_solver = llvm::make_unique<solver::yices_solver_impl>(sem.efac());
    m_smt_path_solver =
        llvm::make_unique<solver::yices_solver_impl>(sem.efac());
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
void PathBmcEngine::to_smt_lib(const ExprVector &f, std::string prefix) {
  assert(SmtOutDir != "");

  std::error_code EC;
  std::string DirName = SmtOutDir;

  // get absolute path to the directory
  SmallVector<char, 256> path;
  EC = sys::fs::make_absolute(DirName, path);
  if (EC) {
    ERR << "Cannot find absolute path to " << DirName;
    return;
  }
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
  raw_fd_ostream fd(fullFilename.toStringRef(path), EC, sys::fs::F_Text);
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

static inline solver::SolverResult path_solver(solver::Solver &solver) {
  Stats::resume("BMC path-based: enumeration path solver");
  auto res = solver.check();
  Stats::stop("BMC path-based: enumeration path solver");
  return res;
}

solver::SolverResult PathBmcEngine::solve() {
  LOG("bmc", get_os(true) << "Starting path-based BMC \n";);

  // -- Precise encoding
  LOG("bmc", get_os(true) << "Begin precise encoding\n";);
  encode();
  LOG("bmc", get_os(true) << "End precise encoding\n";);

  // -- Compute live symbols so that invariant variables exclude
  //    dead variables.
  m_ls.reset(new LiveSymbols(*m_fn, sem().efac(), sem()));
  m_ls->run();

  // -- Heap analysis to improve precision of crab.
  //    Note that this analysis requires the whole module.
  LOG("bmc", get_os(true) << "Begin running memory analysis\n";);
  Stats::resume("BMC path-based: memory analysis");
  m_mem.reset(new clam::SeaDsaHeapAbstraction(*(m_fn->getParent()), m_cg, m_dl,
                                              m_tli, m_awi, false));
  Stats::stop("BMC path-based: memory analysis");
  LOG("bmc", get_os(true) << "End memory analysis\n";);

  clam::CrabBuilderParams  cfg_builder_params;
  cfg_builder_params.simplify = false;
  /// FIXME: the generation of blocking clause from Crab CEX's is not
  /// working. The translation from LLVM to Crab must be changed so
  /// that memory SSA form is not destroyed.
  ///cfg_builder_params.set_array_precision();
  cfg_builder_params.set_num_precision();
  m_cfg_builder_man.reset(new clam::CrabBuilderManager(cfg_builder_params));
  
  // -- Initialize crab for solving paths
  if (UseCrabForSolvingPaths) {
    m_crab_path_solver.reset(new clam::IntraClam(
        *m_fn, m_tli, *m_mem, *m_cfg_builder_man));
  }

  // -- crab invariants
  expr_invariants_map_t invariants;
  // Run whole-program crab analysis and convert invariants to Expr
  if (UseCrabGlobalInvariants) {
    LOG("bmc", get_os(true) << "Begin running crab analysis\n";);
    Stats::resume("BMC path-based: whole-program crab analysis");
    clam::IntraClam crab_analysis(*m_fn, m_tli, *m_mem, *m_cfg_builder_man);

    clam::AnalysisParams params;
    params.dom = CrabDom;
    typename clam::IntraClam::assumption_map_t empty_assumptions;
    crab_analysis.analyze(params, empty_assumptions);
    Stats::stop("BMC path-based: whole-program crab analysis");
    LOG("bmc", get_os(true) << "End running crab analysis\n";);

    LOG("bmc", get_os(true) << "Begin loading of crab global invariants\n";);
    Stats::resume("BMC path-based: loading of crab global invariants");
    load_invariants(crab_analysis, invariants);
    // Assumption: the program has been fully unrolled so there is
    // exactly two cutpoint nodes (entry and exit). We use the symbolic
    // store of the exit node.
    auto &states = getStates();
    if (states.size() == 2) {
      SymStore &s = states[1];
      assert_invariants(invariants, s);
    }
    Stats::stop("BMC path-based: loading of crab global invariants");
    LOG("bmc", get_os(true) << "End loading of crab invariants\n";);
  }

  LOG("bmc-details", for (Expr v
                          : m_precise_side) { errs() << "\t" << *v << "\n"; });

  // -- Boolean abstraction
  LOG("bmc", get_os(true) << "Begin boolean abstraction\n";);
  Stats::resume("BMC path-based: initial boolean abstraction");
  ExprVector abs_side;
  path_bmc::bool_abstraction(m_precise_side, abs_side);
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

    m_result = path_solver(*m_boolean_solver);
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

    expr_invariants_map_t path_constraints;
    if (UseCrabForSolvingPaths) {
      Stats::resume("BMC path-based: solving path + learning clauses with AI");
      bool res = path_encoding_and_solve_with_ai(cex, path_constraints);
      Stats::stop("BMC path-based: solving path + learning clauses with AI");

      LOG("bmc-ai", if (!path_constraints.empty()) {
        errs() << "\nPath constraints (post-conditions) inferred by AI\n";
        for (auto &kv : path_constraints) {
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
        bool ok = block_path();
        if (ok) {
          Stats::count("BMC number symbolic paths discharged by AI");
          continue;
        } else {
          ERR << "Path-based BMC added the same blocking clause again";
          m_result = solver::SolverResult::UNKNOWN;
          return m_result;
        }
      }
    }

    Stats::resume("BMC path-based: solving path + learning clauses with SMT");
    // XXX: the semantics of invariants and path_constraints (e.g.,
    // linear integer arithmetic) might differ from the semantics used
    // by the smt (e.g., bitvectors).
    solver::SolverResult res = path_encoding_and_solve_with_smt(
        cex, invariants, path_constraints /*unused*/);
    Stats::stop("BMC path-based: solving path + learning clauses with SMT");
    if (res == solver::SolverResult::SAT) {
      if (UseCrabForSolvingPaths) {
        // Temporary: for profiling crab
        crab::CrabStats::PrintBrunch(crab::outs());
      }
      m_result = res;
      return res;
    } else {
      // if res is unknown we still add a blocking clause to skip
      // the path.
      bool ok = block_path();
      if (!ok) {
        ERR << "Path-based BMC added the same blocking clause again";
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
        path_bmc::scoped_solver ss(*m_smt_path_solver, timeout);
        res = ss.get().check();
      }
      if (res == solver::SolverResult::SAT) {
        m_model = m_smt_path_solver->get_model();
        if (SmtOutDir != "") {
          to_smt_lib(kv.second, "sat");
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

bool PathBmcEngine::block_path() {
  Stats::resume("BMC path-based: adding blocking clauses");

  // -- Refine the Boolean abstraction
  Expr bc = mk<FALSE>(sem().efac());
  if (m_path_cond.empty()) {
    WARN << "No path condition generated. Trivially unsat ...";
  } else {
    bc = op::boolop::lneg(op::boolop::land(m_path_cond));
  }
  LOG("bmc-details",
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
