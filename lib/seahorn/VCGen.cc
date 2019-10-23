#include "llvm/Support/CommandLine.h"
#include "llvm/Support/FileSystem.h"

#include "seahorn/Analysis/CutPointGraph.hh"
#include "seahorn/Expr/Smt/EZ3.hh"
#include "seahorn/Support/CFG.hh"
#include "seahorn/Support/Stats.hh"
#include "seahorn/VCGen.hh"

#include "seahorn/Expr/ExprOpBinder.hh"
#include "seahorn/Support/SeaDebug.h"

static llvm::cl::opt<bool> EnforceAtMostOnePredecessor(
    "horn-at-most-one-predecessor",
    llvm::cl::desc("Encode a block has at most one predecessor"),
    llvm::cl::init(false), llvm::cl::Hidden);

static llvm::cl::opt<bool> LargeStepReduce(
    "horn-large-reduce",
    llvm::cl::desc("Reduce constraints during large-step encoding"),
    llvm::cl::init(false), llvm::cl::Hidden);

static llvm::cl::opt<bool> UseIte("horn-vcgen-use-ite",
                                  llvm::cl::desc("Use ite-terms in VC"),
                                  llvm::cl::init(false), llvm::cl::Hidden);
static llvm::cl::opt<bool>
    OnlyDataflow("horn-vcgen-only-dataflow",
                 llvm::cl::desc("Encode dataflow dependencies only. Use with "
                                "caution. This option might be unsound or "
                                "imprecise depending on other configurations."),
                 llvm::cl::init(false), llvm::cl::Hidden);

using namespace seahorn;
namespace seahorn {

void VCGen::initSmt(std::unique_ptr<EZ3> &zctx,
                    std::unique_ptr<ZSolver<EZ3>> &smt) {
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

void VCGen::checkSideAtBb(unsigned &head, ExprVector &side, Expr pathCond,
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
  Expr a[1] = {pathCond};

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
    smt.assertExpr(boolop::lneg(pathCond));
    side.push_back(boolop::lneg(pathCond));
  }
}

void VCGen::checkSideAtEnd(unsigned &head, ExprVector &side,
                           ZSolver<EZ3> &smt) {
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
      ctx.setPathCond(trueE);
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

namespace {
bool hasTrackablePhiNode(const BasicBlock &bb, OperationalSemantics &sem) {
  bool hasPhi = false;
  for (const Instruction &inst : bb) {
    if (!isa<PHINode>(&inst))
      break;
    if (sem.isTracked(inst)) {
      return true;
    }
  }
  return false;
}

void computePhiNodeValues(const BasicBlock &bb,
                          const ArrayRef<const BasicBlock *> &preds,
                          ExprVector &edges, OpSemContext &ctx,
                          OperationalSemantics &sem,
                          std::vector<ExprVector> &phiVal) {
  phiVal.resize(preds.size());

  unsigned idx = 0;
  for (const BasicBlock *pred : preds) {
    // clone s
    Stats::resume("vcgen.store.clone");
    SymStore es(ctx.values());
    Stats::stop("vcgen.store.clone");
    // XXX: ctx.fork() is very expensive because it copies complete
    // XXX: content of the symbolic store. Can be fixed with a different
    // interface
    OpSemContextPtr ectx = ctx.fork(es, ctx.side());
    ectx->setPathCond(edges[idx]);

    // edge_ij -> phi_ij,
    // -- definition of phi nodes
    sem.execPhi(bb, *pred, *ectx);
    // -- collect all uses since `es` is local
    ctx.values().uses(ectx->values().uses());

    for (const Instruction &inst : bb) {
      if (!isa<PHINode>(&inst))
        break;
      if (!sem.isTracked(inst))
        continue;

      // -- record the value of PHINode after taking `pred --> bb` edge
      phiVal[idx].push_back(ectx->read(sem.mkSymbReg(inst, ctx)));
    }

    idx++;
  }
}

/// \brief Create definitions for PHINodes using ite expressions
void defPHINodesIte(const BasicBlock &bb, const ExprVector &edges,
                    const std::vector<ExprVector> &phiVal, OpSemContext &ctx,
                    OperationalSemantics &sem) {

  // create symbolic registers for PHINodes
  ExprVector newPhi;
  for (const Instruction &inst : bb) {
    if (!isa<PHINode>(inst))
      break;
    if (!sem.isTracked(inst))
      continue;
    newPhi.push_back(sem.mkSymbReg(inst, ctx));
  }

  assert(edges.size() > 0);
  // TODO: Optimize ite construction by ensuring that each unique value
  // appears only ones. For example, ite(c1, ite(c2, v, u), v) --reduces-->
  // ite (c1 || !c2, v, u) This is easy in this case because conditions are
  // known to be disjoint. This is basically compiling a known switch
  // statement into if-then-else block
  for (unsigned i = 0; i < newPhi.size(); ++i) {
    // assume that path-conditions (edges) are disjoint and that
    // at least one must be true. Using the last edge condition as the
    // default value. If all other edge conditions are false, the default is
    // taken
    Expr val = phiVal[edges.size() - 1][i];
    for (unsigned j = edges.size() - 1; j > 0; --j) {
      val = bind::lite(edges[j - 1], phiVal[j - 1][i], val);
    }
    // write an ite expression as the new PHINode value
    ctx.write(newPhi[i], val);
  }
}

/// \brief Create definitions for PHINodes using equality expressions
void defPHINodesEq(const BasicBlock &bb, const ExprVector &edges,
                   const std::vector<ExprVector> &phiVal, OpSemContext &ctx,
                   OperationalSemantics &sem) {

  // create new havoced values for PHINodes
  ExprVector newPhi;
  for (const Instruction &inst : bb) {
    if (!isa<PHINode>(inst))
      break;
    if (!sem.isTracked(inst))
      continue;
    newPhi.push_back(ctx.havoc(sem.mkSymbReg(inst, ctx)));
  }

  // connect new PHINode register values with constructed PHINode values
  for (unsigned j = 0, sz = edges.size(); j < sz; ++j)
    for (unsigned i = 0, phi_sz = newPhi.size(); i < phi_sz; ++i)
      ctx.addSide(boolop::limp(edges[j], mk<EQ>(newPhi[i], phiVal[j][i])));
}

Expr computePathCondForBb(const BasicBlock &bb, const CpEdge &cpEdge,
                          OpSemContext &ctx, OperationalSemantics &sem) {
  ExprVector edges;
  // -- predicate for reachable from source
  sem_detail::FwdReachPred reachable(cpEdge.parent(), cpEdge.source());

  // compute predecessors relative to the source cut-point
  llvm::SmallVector<const BasicBlock *, 16> preds;
  for (const BasicBlock *p : seahorn::preds(bb))
    if (reachable(p))
      preds.push_back(p);

  // -- compute source of all the edges
  for (const BasicBlock *pred : preds)
    edges.push_back(ctx.read(sem.mkSymbReg(*pred, ctx)));

  assert(preds.size() == edges.size());
  // -- update constant representing current bb
  Expr bbV = ctx.havoc(sem.mkSymbReg(bb, ctx));

  // -- update destination of all the edges

  // -- create edge variables only for critical edges.
  // -- for non critical edges, use (SRC && DST) instead
  for (unsigned i = 0, sz = preds.size(); i < sz; ++i) {
    // -- an edge is non-critical if dst has one predecessor, or src
    // -- has one successor
    if (sz == 1 || preds[i]->getTerminator()->getNumSuccessors() == 1)
      // -- single successor is non-critical
      edges[i] = mk<AND>(bbV, edges[i]);
    // -- critical edge, add edge variable
    else {
      Expr edgV = bind::boolConst(mk<TUPLE>(edges[i], bbV));
      ctx.addSide(mk<IMPL>(edgV, edges[i]));
      edges[i] = edgV;
    }
  }

  // bbV ==> at_least_one(edges)
  // -- encode control flow
  // -- b_j -> (b1 & e_{1,j} | b2 & e_{2,j} | ...)
  ctx.addSide(mk<IMPL>(bbV, mknary<OR>(mk<FALSE>(sem.efac()), edges)));

  // bbv ==> at_most_one(edges)
  if (EnforceAtMostOnePredecessor && edges.size() > 1) {
    // this enforces at-most-one predecessor.
    // if !bbV (i.e., bb is not reachable) then bb won't have
    // predecessors.
    ctx.addSide(mk<IMPL>(bbV, mkAtMostOne(edges)));
  }

  // relate predecessors and conditions under which control flows from them
  unsigned idx = 0;
  for (const BasicBlock *pred : preds) {
    // -- save path condition
    Expr savedPc = ctx.getPathCond();
    // -- set path condition to the current edge
    ctx.setPathCond(edges[idx++]);
    // -- evaluate the condition of the branch
    sem.execBr(*pred, bb, ctx);
    // -- restore path condition
    ctx.setPathCond(savedPc);
  }

  // -- see if there are tracked PHINodes
  // -- compute values of PHINodes
  if (hasTrackablePhiNode(bb, sem)) {
    /// -- generate constraints from the phi-nodes (keep them separate for now)
    // a map from predecessor id to values of all phi-defined variables over
    // that edge for example, phiVal[i][j] is the value of jth PHI-node when
    // control flows from predecessor i
    std::vector<ExprVector> phiVal(preds.size());
    computePhiNodeValues(bb, preds, edges, ctx, sem, phiVal);

    if (UseIte) {
      defPHINodesIte(bb, edges, phiVal, ctx, sem);
    } else {
      defPHINodesEq(bb, edges, phiVal, ctx, sem);
    }
  }

  return bbV;
}
}

void VCGen::genVcForBasicBlockOnEdge(OpSemContext &ctx, const CpEdge &edge,
                                     const BasicBlock &bb, bool last) {

  assert(!last || &bb == &(edge.target().bb()));

  Expr bbV = trueE;

  if (!OnlyDataflow) {
    bbV = computePathCondForBb(bb, edge, ctx, m_sem);
    // unique node with no successors is asserted to always be reachable
    if (last)
      ctx.addSide(bbV);
  }

  // actions of the block. The side-conditions are not guarded by
  // the basic-block variable because it does not matter.
  if (!last) {
    m_sem.exec(bb, ctx.pc(bbV));
  } else if (const TerminatorInst *term = bb.getTerminator()) {
    if (isa<UnreachableInst>(term))
      m_sem.exec(bb, ctx.pc(trueE));
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
