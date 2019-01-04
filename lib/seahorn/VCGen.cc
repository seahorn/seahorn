#include "llvm/Support/CommandLine.h"
#include "llvm/Support/FileSystem.h"

#include "seahorn/Analysis/CutPointGraph.hh"
#include "seahorn/Support/CFG.hh"
#include "seahorn/Support/Stats.hh"
#include "seahorn/VCGen.hh"
#include "ufo/Smt/EZ3.hh"

#include "seahorn/Support/SeaDebug.h"

static llvm::cl::opt<bool> SplitCriticalEdgesOnly(
    "horn-split-only-critical",
    llvm::cl::desc("Introduce edge variables only for critical edges"),
    llvm::cl::init(true), llvm::cl::Hidden);

static llvm::cl::opt<bool> EnforceAtMostOnePredecessor(
    "horn-at-most-one-predecessor",
    llvm::cl::desc("Encode a block has at most one predecessor"),
    llvm::cl::init(false), llvm::cl::Hidden);

static llvm::cl::opt<bool> LargeStepReduce(
    "horn-large-reduce",
    llvm::cl::desc("Reduce constraints during large-step encoding"),
    llvm::cl::init(false), llvm::cl::Hidden);

using namespace ufo;
namespace seahorn {

void VCGen::initSmt(std::unique_ptr<ufo::EZ3> &zctx,
                    std::unique_ptr<ufo::ZSolver<ufo::EZ3>> &smt) {
  if (!LargeStepReduce)
    return;
  errs() << "\nE";
  // XXX Consider using global EZ3
  zctx.reset(new EZ3(m_sem.efac()));
  smt.reset(new ZSolver<EZ3>(*zctx));
  ZParams<EZ3> params(*zctx);
  params.set(":smt.array.weak", true);
  params.set(":smt.arith.ignore_int", true);
  smt->set(params);
}

void VCGen::checkSideAtBb(unsigned &head, ExprVector &side, Expr bbV,
                          ZSolver<EZ3> &smt, const CpEdge &edge,
                          const BasicBlock &bb) {
  if (!LargeStepReduce)
    return;
  bind::IsConst isConst;

  for (unsigned sz = side.size(); head < sz; ++head) {
    ScopedStats __st__("VCGen.smt");
    Expr e = side[head];
    if (!bind::isFapp(e) || isConst(e))
      smt.assertExpr(e);
  }

  errs() << ".";
  errs().flush();

  TimeIt<llvm::raw_ostream &> _t_("smt-solving", errs(), 0.1);

  ScopedStats __st__("VCGen.smt");
  Expr a[1] = {bbV};

  LOG("pedge", std::error_code EC;
      raw_fd_ostream file("/tmp/p-edge.smt2", EC, sys::fs::F_Text); if (!EC) {
        file << "(set-info :original \"" << edge.source().bb().getName()
             << " --> " << bb.getName() << " --> "
             << edge.target().bb().getName() << "\")\n";
        smt.toSmtLibAssuming(file, a);
        file.close();
      });

  auto res = smt.solveAssuming(a);
  if (!res) {
    errs() << "F";
    errs().flush();
    Stats::count("VCGen.smt.unsat");
    smt.assertExpr(boolop::lneg(bbV));
    side.push_back(boolop::lneg(bbV));
  }
}

void VCGen::checkSideAtEnd(unsigned &head, ExprVector &side,
                           ufo::ZSolver<ufo::EZ3> &smt) {
  if (!LargeStepReduce)
    return;
  bind::IsConst isConst;
  for (unsigned sz = side.size(); head < sz; ++head) {
    ScopedStats __st__("VCGen.smt");
    Expr e = side[head];
    if (!bind::isFapp(e) || isConst(e))
      smt.assertExpr(e);
  }

  ScopedStats __st__("VCGen.smt.last");
  auto res = smt.solve();
  if (!res) {
    Stats::count("VCGen.smt.last.unsat");
    side.push_back(mk<FALSE>(m_sem.efac()));
  }
}

void VCGen::genVcForCpEdgeLegacy(SymStore &s, const CpEdge &edge,
                                 ExprVector &side) {
  OpSemContextPtr ctx = m_sem.mkContext(s, side);
  genVcForCpEdge(*ctx, edge);
}

void VCGen::genVcForCpEdge(OpSemContext &ctx, const CpEdge &edge) {
  const CutPoint &target = edge.target();

  std::unique_ptr<EZ3> zctx(nullptr);
  std::unique_ptr<ZSolver<EZ3>> smt(nullptr);
  initSmt(zctx, smt);

  // remember what was added since last call to smt
  unsigned head = ctx.side().size();

  bool isEntry = true;
  for (const BasicBlock &bb : edge) {
    Expr bbV;
    if (isEntry) {
      // -- initialize bb-exec register
      bbV = ctx.havoc(m_sem.mkSymbReg(bb, ctx));
      // -- compute side-conditions for the entry block of the edge
      ctx.setActLit(trueE);
      m_sem.exec(bb, ctx);
    } else {
      // -- generate side-conditions for bb
      genVcForBasicBlockOnEdge(ctx, edge, bb);
      // -- check current value of bb-exec register
      bbV = ctx.read(m_sem.mkSymbReg(bb, ctx));
    }
    isEntry = false;

    // -- check that the current side condition is consistent
    if (smt)
      checkSideAtBb(head, ctx.side(), bbV, *smt, edge, bb);
  }

  // -- generate side condition for the last basic block on the edge
  // -- this executes only PHINode instructions in target.bb()
  genVcForBasicBlockOnEdge(ctx, edge, target.bb(), true);

  // -- check consistency of side-conditions at the end
  if (smt)
    checkSideAtEnd(head, ctx.side(), *smt);
}

namespace sem_detail {
struct FwdReachPred : public std::unary_function<const BasicBlock &, bool> {
  const CutPointGraph &m_cpg;
  const CutPoint &m_cp;

  FwdReachPred(const CutPointGraph &cpg, const CutPoint &cp)
      : m_cpg(cpg), m_cp(cp) {}

  bool operator()(const BasicBlock &bb) const {
    return m_cpg.isFwdReach(m_cp, bb);
  }
  bool operator()(const BasicBlock *bb) const { return this->operator()(*bb); }
};
} // namespace sem_detail

/// \brief Naive quadratic implementation of at-most-one
static Expr mkAtMostOne(ExprVector &vec) {
  assert(!vec.empty());
  ExprVector res;
  for (unsigned i = 0, e = vec.size(); i < e; ++i) {
    ExprVector exactly_vi; // exactly  vec[i]
    exactly_vi.push_back(vec[i]);
    for (unsigned j = 0; j < e; ++j) {
      if (vec[i] == vec[j])
        continue;
      exactly_vi.push_back(mk<NEG>(vec[j]));
    }
    // at this point: exactly_vi is vi && !vj for all j
    res.push_back(op::boolop::land(exactly_vi));
  }
  return mknary<OR>(res);
}

void VCGen::genVcForBasicBlockOnEdge(OpSemContext &ctx, const CpEdge &edge,
                                     const BasicBlock &bb, bool last) {
  ExprVector edges;

  if (last)
    assert(&bb == &(edge.target().bb()));

  // -- predicate for reachable from source
  sem_detail::FwdReachPred reachable(edge.parent(), edge.source());

  // compute predecessors, relative to the source cut-point
  llvm::SmallVector<const BasicBlock *, 16> preds;
  for (const BasicBlock *p : seahorn::preds(bb))
    if (reachable(p))
      preds.push_back(p);

  // -- compute source of all the edges
  for (const BasicBlock *pred : preds)
    edges.push_back(ctx.read(m_sem.mkSymbReg(*pred, ctx)));

  assert(preds.size() == edges.size());
  // -- update constant representing current bb
  Expr bbV = ctx.havoc(m_sem.mkSymbReg(bb, ctx));

  // -- update destination of all the edges

  if (SplitCriticalEdgesOnly) {
    // -- create edge variables only for critical edges.
    // -- for non critical edges, use (SRC && DST) instead

    for (unsigned i = 0, e = preds.size(); i < e; ++i) {
      // -- an edge is non-critical if dst has one predecessor, or src
      // -- has one successor
      if (e == 1 || preds[i]->getTerminator()->getNumSuccessors() == 1)
        // -- single successor is non-critical
        edges[i] = mk<AND>(bbV, edges[i]);
      else // -- critical edge, add edge variable
      {
        Expr edgV = bind::boolConst(mk<TUPLE>(edges[i], bbV));
        ctx.addSide(mk<IMPL>(edgV, edges[i]));
        edges[i] = mk<AND>(edges[i], edgV);
      }
    }
  } else {
    // -- b_i & e_{i,j}
    for (Expr &e : edges)
      e = mk<AND>(e, bind::boolConst(mk<TUPLE>(e, bbV)));
  }

  if (EnforceAtMostOnePredecessor && edges.size() > 1) {
    // this enforces at-most-one predecessor.
    // if !bbV (i.e., bb is not reachable) then bb won't have
    // predecessors.
    ctx.addSide(mk<IMPL>(bbV, mkAtMostOne(edges)));
  }

  // -- encode control flow
  // -- b_j -> (b1 & e_{1,j} | b2 & e_{2,j} | ...)
  ctx.addSide(mk<IMPL>(bbV, mknary<OR>(mk<FALSE>(m_sem.efac()), edges)));

  // unique node with no successors is asserted to always be reachable
  if (last)
    ctx.addSide(bbV);

  /// -- generate constraints from the phi-nodes (keep them separate for now)
  std::vector<ExprVector> phiConstraints(preds.size());

  unsigned idx = 0;
  for (const BasicBlock *pred : preds) {
    // clone s
    SymStore es(ctx.values());
    OpSemContextPtr ectx = ctx.fork(es, ctx.side());
    ectx->setActLit(edges[idx]);

    // edge_ij -> phi_ij,
    // -- branch condition
    m_sem.execBr(*pred, bb, *ectx);
    // -- definition of phi nodes
    m_sem.execPhi(bb, *pred, *ectx);
    // -- collect all uses since `es` is local
    ctx.values().uses(ectx->values().uses());

    for (const Instruction &inst : bb) {
      if (!isa<PHINode>(&inst))
        break;
      if (!m_sem.isTracked(inst))
        continue;

      // -- record the value of PHINode after taking `pred --> bb` edge
      phiConstraints[idx].push_back(ectx->read(m_sem.mkSymbReg(inst, ctx)));
    }

    idx++;
  }

  // create new values for PHINode registers
  ExprVector newPhi;
  for (const Instruction &inst : bb) {
    if (!isa<PHINode>(inst))
      break;
    if (!m_sem.isTracked(inst))
      continue;
    newPhi.push_back(ctx.havoc(m_sem.mkSymbReg(inst, ctx)));
  }

  // connect new PHINode register values with constructed PHINode values
  for (unsigned j = 0; j < edges.size(); ++j)
    for (unsigned i = 0; i < newPhi.size(); ++i)
      ctx.addSide(
          boolop::limp(edges[j], mk<EQ>(newPhi[i], phiConstraints[j][i])));

  // actions of the block. The side-conditions are not guarded by
  // the basic-block variable because it does not matter.
  if (!last) {
    m_sem.exec(bb, ctx.act(bbV));
  } else if (const TerminatorInst *term = bb.getTerminator()) {
    if (isa<UnreachableInst>(term))
      m_sem.exec(bb, ctx.act(trueE));
  }
}

// 1. execute all basic blocks using small-step semantics in topological order

// 2. when a block executes, it updates a special variable for the block

// 3. allocate a Boolean variable for each edge: these are unique
// if named using bb variables

// 4. side condition: edge -> branchCond & execPhi

// actions: optionally conditional on the block
// bb_i -> e_i1 | e_i2 | e_i3
// e_i1 -> bb_1
// e_i1 -> brcond (i, 1)
// e_i1 -> phi_1(i)
} // namespace seahorn
