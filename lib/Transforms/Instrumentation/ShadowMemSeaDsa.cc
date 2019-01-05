#include "seahorn/Transforms/Instrumentation/ShadowMemSeaDsa.hh"
#include "llvm/ADT/SCCIterator.h"
#include "llvm/ADT/STLExtras.h"
#include "llvm/Analysis/AssumptionCache.h"
#include "llvm/Analysis/CallGraph.h"
#include "llvm/Analysis/MemoryBuiltins.h"
#include "llvm/Analysis/TargetLibraryInfo.h"
#include "llvm/IR/DataLayout.h"
#include "llvm/IR/Dominators.h"
#include "llvm/IR/IRBuilder.h"
#include "llvm/IR/InstIterator.h"
#include "llvm/IR/IntrinsicInst.h"
#include "llvm/IR/Verifier.h"
#include "llvm/Support/raw_ostream.h"
#include "llvm/Transforms/Utils/BasicBlockUtils.h"
#include "llvm/Transforms/Utils/Local.h"
#include "llvm/Transforms/Utils/PromoteMemToReg.h"

#include "boost/range.hpp"
#include "boost/range/algorithm/binary_search.hpp"
#include "boost/range/algorithm/set_algorithm.hpp"
#include "boost/range/algorithm/sort.hpp"
#include "seahorn/Support/SeaDebug.h"
#include "seahorn/Transforms/Utils/Local.hh"

#include "sea_dsa/CallSite.hh"
#include "sea_dsa/DsaAnalysis.hh"
#include "sea_dsa/Mapper.hh"
#include "seahorn/Support/SeaLog.hh"
#include "seahorn/Support/SortTopo.hh"

llvm::cl::opt<bool> SplitFields("horn-sea-dsa-split",
                                llvm::cl::desc("DSA: Split nodes by fields"),
                                llvm::cl::init(false));

llvm::cl::opt<bool>
    LocalReadMod("horn-sea-dsa-local-mod",
                 llvm::cl::desc("DSA: Compute read/mod info locally"),
                 llvm::cl::init(false));

using namespace llvm;
namespace dsa = sea_dsa;
namespace {
Value *getUniqueScalar(LLVMContext &ctx, IRBuilder<> &B, const dsa::Cell &c) {
  const dsa::Node *n = c.getNode();
  if (n && c.getOffset() == 0) {
    Value *v = const_cast<Value *>(n->getUniqueScalar());

    // -- a unique scalar is a single-cell global variable. We might be
    // -- able to extend this to single-cell local pointers, but these
    // -- are probably not very common.
    if (v)
      if (GlobalVariable *gv = dyn_cast<GlobalVariable>(v))
        if (gv->getType()->getElementType()->isSingleValueType())
          return B.CreateBitCast(v, Type::getInt8PtrTy(ctx));
  }
  return ConstantPointerNull::get(Type::getInt8PtrTy(ctx));
}

template <typename Set> void markReachableNodes(const dsa::Node *n, Set &set) {
  if (!n)
    return;
  assert(!n->isForwarding() && "Cannot mark a forwarded node");

  if (set.insert(n).second)
    for (auto const &edg : n->links())
      markReachableNodes(edg.second->getNode(), set);
}

template <typename Set>
void reachableNodes(const Function &fn, dsa::Graph &g, Set &inputReach,
                    Set &retReach) {
  // formal parameters
  for (Function::const_arg_iterator I = fn.arg_begin(), E = fn.arg_end();
       I != E; ++I) {
    const Value &arg = *I;
    if (g.hasCell(arg)) {
      dsa::Cell &c = g.mkCell(arg, dsa::Cell());
      markReachableNodes(c.getNode(), inputReach);
    }
  }

  // globals
  for (auto &kv : llvm::make_range(g.globals_begin(), g.globals_end()))
    markReachableNodes(kv.second->getNode(), inputReach);

  // return value
  if (g.hasRetCell(fn))
    markReachableNodes(g.getRetCell(fn).getNode(), retReach);
}

template <typename Set> void set_difference(Set &s1, Set &s2) {
  Set s3;
  boost::set_difference(s1, s2, std::inserter(s3, s3.end()));
  std::swap(s3, s1);
}

template <typename Set> void set_union(Set &s1, Set &s2) {
  Set s3;
  boost::set_union(s1, s2, std::inserter(s3, s3.end()));
  std::swap(s3, s1);
}

/// Computes Node reachable from the call arguments in the graph.
/// reach - all reachable nodes
/// outReach - subset of reach that is only reachable from the return node
template <typename Set1, typename Set2>
void argReachableNodes(const Function &fn, dsa::Graph &G, Set1 &reach,
                       Set2 &outReach) {
  reachableNodes(fn, G, reach, outReach);
  set_difference(outReach, reach);
  set_union(reach, outReach);
}

class ShadowDsaImpl : public InstVisitor<ShadowDsaImpl> {

  dsa::GlobalAnalysis &m_dsa;
  TargetLibraryInfo *m_tli;
  CallGraph *m_callGraph;
  Pass &m_pass;

  bool m_splitDsaNodes;
  bool m_computeReadMod;

  llvm::Constant *m_memLoadFn = nullptr;
  llvm::Constant *m_memStoreFn = nullptr;
  llvm::Constant *m_memTrsfrLoadFn = nullptr;
  llvm::Constant *m_memShadowInitFn = nullptr;
  llvm::Constant *m_memShadowUniqInitFn = nullptr;

  llvm::Constant *m_memShadowArgInitFn = nullptr;
  llvm::Constant *m_memShadowUniqArgInitFn = nullptr;

  llvm::Constant *m_argRefFn = nullptr;
  llvm::Constant *m_argModFn = nullptr;
  llvm::Constant *m_argNewFn = nullptr;

  llvm::Constant *m_markIn = nullptr;
  llvm::Constant *m_markOut = nullptr;
  llvm::Constant *m_markUniqIn = nullptr;
  llvm::Constant *m_markUniqOut = nullptr;

  llvm::Constant *m_memGlobalVarInitFn = nullptr;

  using ShadowsMap =
      llvm::DenseMap<const sea_dsa::Node *,
                     llvm::DenseMap<unsigned, llvm::AllocaInst *>>;
  using NodeIdMap = llvm::DenseMap<const sea_dsa::Node *, unsigned>;

  /// \brief A map from DsaNode to all the shadow pseudo-variable corresponding
  /// to it
  ///
  /// If \f m_splitDsaNodes is false, each DsaNode has a single shadow variable
  /// If
  /// \f m_splitDsaNodes is true, each field in the node has a shadow variable.
  /// Thus
  /// the map connects a node to a pair of an offset and an AllocaInst that
  /// corresponds to the shadow variable
  ShadowsMap m_shadows;

  /// \brief A map from DsaNode to its numeric id
  NodeIdMap m_nodeIds;

  /// \brief The largest id used so far. Used to allocate fresh ids
  unsigned m_maxId = 0;

  /// \brief A pointer to i32 type for convenience
  llvm::Type *m_Int32Ty;

  /// Used by doReadMod
  using NodeSet = boost::container::flat_set<const sea_dsa::Node *>;
  using NodeSetMap = llvm::DenseMap<const llvm::Function *, NodeSet>;
  /// \brief A map from Function to all DsaNode that are read by it
  NodeSetMap m_readList;
  /// \brief A map from Function to all DsaNode that are written by it
  NodeSetMap m_modList;

  // -- temporaries, used by visitor
  llvm::LLVMContext *m_llvmCtx = nullptr;
  std::unique_ptr<IRBuilder<>> m_B = nullptr;
  dsa::Graph *m_graph;

private:
  /// \brief Create shadow pseudo-functions in the module
  void mkShadowFunctions(Module &M);

  /// \brief Re-compute read/mod information for each function
  ///
  /// This only makes sense for context-insensitive SeaDsa under which all
  /// functions share the same DsaGraph. In this case, the Mod/Ref information
  /// in the graph is common to all functions. This procedure recomputes the
  /// Mod/Ref information locally by traversing all the functions bottom up in
  /// the call graph order.
  ///
  /// The procedure is unsound if used together with context-sensitive mode of
  /// SeaDsa
  void doReadMod();

  /// \brief Computes Mod/Ref sets for the given function \p F
  void updateReadMod(Function &F, NodeSet &readSet, NodeSet &modSet);

  /// \brief Returns the offset of the field pointed by \p c
  ///
  /// Returns 0 if \f m_splitDsaNodes is false
  unsigned getOffset(const dsa::Cell &c) {
    return m_splitDsaNodes ? c.getOffset() : 0;
  }

  /// \breif Returns a local id of a given field of DsaNode \p n
  unsigned getFieldId(const dsa::Node &n, unsigned offset) {
    auto it = m_nodeIds.find(&n);
    if (it != m_nodeIds.end())
      return it->second + offset;

    // allocate new id for the node
    unsigned id = m_maxId;
    m_nodeIds[&n] = id;
    if (n.size() == 0) {
      // XXX: what does it mean for a node to have 0 size?
      assert(offset == 0);
      m_maxId++;
      return id;
    }

    // -- allocate enough ids for the node and all its fields
    m_maxId += n.size();
    return id + offset;
    return 0;
  }

  /// \breif Returns id of a field pointed to by the given cell \c
  unsigned getFieldId(const dsa::Cell &c) {
    assert(c.getNode());
    return getFieldId(*c.getNode(), getOffset(c));
  }

  /// \brief Returns shadow variable for a given field
  AllocaInst *getShadowForField(const dsa::Node &n, unsigned offset) {
    auto &offsetMap = m_shadows[&n];
    auto it = offsetMap.find(offset);
    if (it != offsetMap.end())
      return it->second;

    // -- not found, allocate new shadow variable
    AllocaInst *inst = new AllocaInst(m_Int32Ty, 0 /* Address Space */);
    // -- inst is eventually added to the Module and it will take ownership
    offsetMap[offset] = inst;
    return inst;
  }

  /// \breif Returns shadow variable for a field pointed to by a cell \p cell
  AllocaInst *getShadowForField(const dsa::Cell &cell) {
    return getShadowForField(*cell.getNode(), getOffset(cell));
    assert(cell.getNode());
  }

  bool isRead(const dsa::Cell &c, const Function &f) {
    return c.getNode() ? isRead(c.getNode(), f) : false;
  }
  bool isModified(const dsa::Cell &c, const Function &f) {
    return c.getNode() ? isModified(c.getNode(), f) : false;
  }
  bool isRead(const dsa::Node *n, const Function &f) {
    LOG("shadow_mod",
        if (m_computeReadMod && n->isRead() != (m_readList[&f].count(n) > 0)) {
          errs() << f.getName() << " readNode: " << n->isRead()
                 << " readList: " << m_readList[&f].count(n) << "\n";
          if (n->isRead())
            n->write(errs());
        });
    return m_computeReadMod ? m_readList[&f].count(n) > 0 : n->isRead();
  }
  bool isModified(const dsa::Node *n, const Function &f) {
    LOG("shadow_mod", if (m_computeReadMod &&
                          n->isModified() != (m_modList[&f].count(n) > 0)) {
      errs() << f.getName() << " modNode: " << n->isModified()
             << " modList: " << m_modList[&f].count(n) << "\n";
      if (n->isModified())
        n->write(errs());
    });
    return m_computeReadMod ? m_modList[&f].count(n) > 0 : n->isModified();
  }

  void markCall(CallInst *ci) {
    // use ci->getMetadata(seahorn) to test.
    Module *m = ci->getParent()->getParent()->getParent();
    MDNode *meta = MDNode::get(m->getContext(), None);
    ci->setMetadata("shadow.mem", meta);
  }

  CallInst *mkShadowAllocInit(IRBuilder<> &B, Constant *fn, AllocaInst *a,
                              const dsa::Cell &c) {
    B.Insert(a, "shadow.mem." + Twine(getFieldId(c)));
    CallInst *ci;
    Value *us = getUniqueScalar(*m_llvmCtx, B, c);
    ci = B.CreateCall(fn, {B.getInt32(getFieldId(c)), us}, "sm");
    markCall(ci);
    B.CreateStore(ci, a);
    return ci;
  }
  StoreInst *mkShadowStore(IRBuilder<> &B, const dsa::Cell &c) {
    AllocaInst *v = getShadowForField(c);
    return B.CreateStore(mkStoreFnCall(B, c, v), v);
  }

  CallInst *mkStoreFnCall(IRBuilder<> &B, const dsa::Cell &c, AllocaInst *v) {
    auto *ci = B.CreateCall(m_memStoreFn,
                            {m_B->getInt32(getFieldId(c)), m_B->CreateLoad(v),
                             getUniqueScalar(*m_llvmCtx, B, c)},
                            "sm");
    markCall(ci);
    return ci;
  }

  void mkShadowGlobalVarInit(IRBuilder<> &B, const dsa::Cell &c) {
    auto *v = getShadowForField(c);
    auto *ci = B.CreateCall(m_memGlobalVarInitFn,
                            {m_B->getInt32(getFieldId(c)), m_B->CreateLoad(v),
                             getUniqueScalar(*m_llvmCtx, B, c)},
                            "sm");
    markCall(ci);
  }
  void mkShadowLoad(IRBuilder<> &B, const dsa::Cell &c) {
    auto *ci = B.CreateCall(m_memLoadFn, {B.getInt32(getFieldId(c)),
                                          B.CreateLoad(getShadowForField(c)),
                                          getUniqueScalar(*m_llvmCtx, B, c)});
    markCall(ci);
  }

  void mkShadowMemTrsfr(IRBuilder<> &B, const dsa::Cell &dst,
                        const dsa::Cell &src) {
    // insert memtrfr.load for the read access
    auto *ci =
        B.CreateCall(m_memTrsfrLoadFn, {B.getInt32(getFieldId(src)),
                                        B.CreateLoad(getShadowForField(src)),
                                        getUniqueScalar(*m_llvmCtx, B, src)});
    markCall(ci);

    // insert normal mem.store for the write access
    mkShadowStore(B, dst);
  }

  void mkArgRef(IRBuilder<> &B, const dsa::Cell &c, unsigned idx) {
    AllocaInst *v = getShadowForField(c);
    unsigned id = getFieldId(c);
    auto *ci = B.CreateCall(m_argRefFn, {B.getInt32(id), m_B->CreateLoad(v),
                                         m_B->getInt32(idx),
                                         getUniqueScalar(*m_llvmCtx, B, c)});
    markCall(ci);
  }
  void mkArgNewMod(IRBuilder<> &B, Constant *argFn, const dsa::Cell &c,
                   unsigned idx) {
    AllocaInst *v = getShadowForField(c);
    unsigned id = getFieldId(c);
    auto *ci = B.CreateCall(argFn,
                            {B.getInt32(id), B.CreateLoad(v), B.getInt32(idx),
                             getUniqueScalar(*m_llvmCtx, B, c)},
                            "sh");
    B.CreateStore(ci, v);
    markCall(ci);
  }
  void mkMarkIn(IRBuilder<> &B, const dsa::Cell &c, Value *v, unsigned idx) {
    auto *ci =
        B.CreateCall(m_markIn, {B.getInt32(getFieldId(c)), v, B.getInt32(idx),
                                getUniqueScalar(*m_llvmCtx, B, c)});
    markCall(ci);
  }
  void mkMarkOut(IRBuilder<> &B, const dsa::Cell &c, unsigned idx) {
    auto *ci = B.CreateCall(m_markOut, {B.getInt32(getFieldId(c)),
                                        B.CreateLoad(getShadowForField(c)),
                                        B.getInt32(idx),
                                        getUniqueScalar(*m_llvmCtx, B, c)});
    markCall(ci);
  }

  void runMem2Reg(Function &F) {
    std::vector<AllocaInst *> allocas;

    // -- for every node
    for (auto &kv : m_shadows) {
      // -- for every offset
      for (auto &entry : kv.second) {
        // -- only take allocas that are in some basic block
        if (entry.second->getParent())
          allocas.push_back(entry.second);
      }
    }

    DominatorTree &DT =
        m_pass.getAnalysis<llvm::DominatorTreeWrapperPass>(F).getDomTree();
    AssumptionCache &AC =
        m_pass.getAnalysis<llvm::AssumptionCacheTracker>().getAssumptionCache(
            F);
    PromoteMemToReg(allocas, DT, &AC);
  }

  /// \brief Infer which PHINodes corresponds to shadow pseudo-assignments
  /// The type is stored as a meta-data on the node
  void inferTypeOfPHINodes(Function &F) {
    // -- order blocks in (rev)topological order
    std::vector<const BasicBlock *> order;
    seahorn::RevTopoSort(F, order);

    // for every bb in topological order
    for (auto *bb : llvm::reverse(order)) {
      // for every PHINode
      for (auto &phi : bb->phis()) {
        // for every incoming value
        for (auto &val : phi.incoming_values()) {
          // if an incoming value has metadata, take it, and be done
          if (auto *inst = dyn_cast<const Instruction>(&val)) {
            if (auto *meta = inst->getMetadata("shadow.mem")) {
              const_cast<PHINode *>(&phi)->setMetadata("shadow.mem", meta);
              break;
            }
          }
        }
      }
    }
  }

public:
  ShadowDsaImpl(dsa::GlobalAnalysis &dsa, TargetLibraryInfo *tli, CallGraph *cg,
                Pass &pass, bool splitDsaNodes = false,
                bool computeReadMod = false)
      : m_dsa(dsa), m_tli(tli), m_callGraph(cg), m_pass(pass),
        m_splitDsaNodes(splitDsaNodes), m_computeReadMod(computeReadMod) {}

  bool runOnModule(Module &M) {
    if (m_computeReadMod)
      doReadMod();

    mkShadowFunctions(M);
    m_nodeIds.clear();
    for (Function &F : M)
      runOnFunction(F);
    return false;
  };

  bool runOnFunction(Function &F);
  void visitFunction(Function &F);
  void visitMainFunction(Function &F);
  void visitAllocaInst(AllocaInst &I);
  void visitLoadInst(LoadInst &I);
  void visitStoreInst(StoreInst &I);
  void visitCallSite(CallSite CS);
  void visitMemSetInst(MemSetInst &I);
  void visitMemTransferInst(MemTransferInst &I);
  void visitAllocationFn(CallSite &CS);
  void visitCalloc(CallSite &CS);
  void visitDsaCallSite(dsa::DsaCallSite &CS);
};

bool ShadowDsaImpl::runOnFunction(Function &F) {
  if (F.isDeclaration())
    return false;

  if (!m_dsa.hasGraph(F))
    return false;

  m_graph = &m_dsa.getGraph(F);
  m_shadows.clear();

  // -- instrument function F with pseudo-instructions
  m_llvmCtx = &F.getContext();
  m_B = llvm::make_unique<IRBuilder<>>(*m_llvmCtx);

  this->visit(F);

  auto &B = *m_B;
  auto &ctx = *m_llvmCtx;
  auto &G = *m_graph;
  // -- compute pseudo-functions for inputs and outputs

  // compute Nodes that escape because they are either reachable
  // from the input arguments or from returns
  std::set<const dsa::Node *> reach;
  std::set<const dsa::Node *> retReach;
  argReachableNodes(F, G, reach, retReach);

  // -- create shadows for all nodes that are modified by this
  // -- function and escape to a parent function
  for (const dsa::Node *n : reach)
    if (isModified(n, F) || isRead(n, F)) {
      // TODO: allocate for all slices of n, not just offset 0
      getShadowForField(*n, 0);
    }

  // allocate initial value for all used shadows
  DenseMap<const dsa::Node *, DenseMap<unsigned, Value *>> inits;
  B.SetInsertPoint(&*F.getEntryBlock().begin());
  for (auto it : m_shadows) {
    const dsa::Node *n = it.first;

    Constant *fn =
        reach.count(n) <= 0 ? m_memShadowInitFn : m_memShadowArgInitFn;

    for (auto jt : it.second) {
      dsa::Cell c(const_cast<dsa::Node *>(n), jt.first);
      AllocaInst *a = jt.second;
      inits[c.getNode()][getOffset(c)] = mkShadowAllocInit(B, fn, a, c);
    }
  }

  ReturnInst *_ret = nullptr;
  seahorn::HasReturn(F, _ret);
  if (!_ret) {
    // TODO: Need to think how to handle functions that do not return in
    // interprocedural encoding. For now, we print a warning and ignore this
    // case.
    WARN << "Function " << F.getName()
         << "never returns."
            "Inter-procedural analysis with such functions might not be "
            "supported.";
    return true;
  }
  TerminatorInst *ret = cast<ReturnInst>(_ret);
  BasicBlock *exit = ret->getParent();

  // split return basic block if it has more than just the return instruction
  if (exit->size() > 1) {
    exit = llvm::SplitBlock(exit, ret,
                            // these two passes will not be preserved if null
                            nullptr /*DominatorTree*/, nullptr /*LoopInfo*/);
    ret = exit->getTerminator();
  }

  B.SetInsertPoint(ret);
  unsigned idx = 0;
  for (const dsa::Node *n : reach) {
    // TODO: extend to work with all slices
    dsa::Cell c(const_cast<dsa::Node *>(n), 0);

    // n is read and is not only return-node reachable (for
    // return-only reachable nodes, there is no initial value
    // because they are created within this function)
    if ((isRead(n, F) || isModified(n, F)) && retReach.count(n) <= 0) {
      assert(!inits[n].empty());
      /// initial value
      mkMarkIn(B, c, inits[n][0], idx);
    }

    if (isModified(n, F)) {
      assert(!inits[n].empty());
      /// final value
      mkMarkOut(B, c, idx);
    }
    ++idx;
  }

  // -- convert new allocas to registers
  runMem2Reg(F);
  // -- infer types for PHINodes
  inferTypeOfPHINodes(F);

  m_B.reset(nullptr);
  m_llvmCtx = nullptr;
  m_graph = nullptr;
  m_shadows.clear();
  return true;
}

void ShadowDsaImpl::visitFunction(Function &fn) {
  if (fn.getName().equals("main")) {
    visitMainFunction(fn);
  }
}
void ShadowDsaImpl::visitMainFunction(Function &fn) {}
void ShadowDsaImpl::visitAllocaInst(AllocaInst &I) {
  if (!m_graph->hasCell(I))
    return;

  const dsa::Cell &c = m_graph->getCell(I);
  if (c.isNull())
    return;

  m_B->SetInsertPoint(&I);
  mkShadowLoad(*m_B, c);
}

void ShadowDsaImpl::visitLoadInst(LoadInst &I) {
  if (!m_graph->hasCell(*(I.getOperand(0))))
    return;
  const dsa::Cell &c = m_graph->getCell(*(I.getOperand(0)));
  if (c.isNull())
    return;

  m_B->SetInsertPoint(&I);
  mkShadowLoad(*m_B, c);
}
void ShadowDsaImpl::visitStoreInst(StoreInst &I) {
  if (!m_graph->hasCell(*(I.getOperand(1))))
    return;
  const dsa::Cell &c = m_graph->getCell(*(I.getOperand(1)));
  if (c.isNull())
    return;

  m_B->SetInsertPoint(&I);
  mkShadowStore(*m_B, c);
}
void ShadowDsaImpl::visitCallSite(CallSite CS) {
  if (CS.isIndirectCall())
    return;

  if (auto *fn = CS.getCalledFunction()) {
    if ((fn->getName().startswith("seahorn.") ||
         fn->getName().startswith("verifier.")) &&
        /* seahorn.bounce should be treated as a regular function*/
        !(fn->getName().startswith("seahorn.bounce")))
      return;
  }

  LOG("shadow_cs", errs() << "Call: " << *CS.getInstruction() << "\n";);

  ImmutableCallSite ics(CS.getInstruction());
  dsa::DsaCallSite dcs(ics);

  if (!dcs.getCallee())
    return;

  if (dcs.getCallee()->getName().equals("calloc")) {
    visitCalloc(CS);
    return;
  }

  if (m_tli && llvm::isAllocationFn(CS.getInstruction(), m_tli, true)) {
    visitAllocationFn(CS);
    return;
  }

  const Function &CF = *dcs.getCallee();
  if (m_dsa.hasGraph(CF)) {
    visitDsaCallSite(dcs);
    return;
  }
}

void ShadowDsaImpl::visitDsaCallSite(dsa::DsaCallSite &CS) {
  const Function &CF = *CS.getCallee();

  dsa::Graph &calleeG = m_dsa.getGraph(CF);

  // -- compute callee nodes reachable from arguments and returns
  std::set<const dsa::Node *> reach;
  std::set<const dsa::Node *> retReach;
  argReachableNodes(CF, calleeG, reach, retReach);

  // -- compute mapping between callee and caller graphs
  dsa::SimulationMapper simMap;
  dsa::Graph::computeCalleeCallerMapping(CS, calleeG, *m_graph, simMap);

  /// generate mod, ref, new function, based on whether the
  /// remote node reads, writes, or creates the corresponding node.

  m_B->SetInsertPoint(const_cast<Instruction *>(CS.getInstruction()));
  unsigned idx = 0;
  for (const dsa::Node *n : reach) {
    LOG("global_shadow", errs() << *n << "\n";
        const Value *v = n->getUniqueScalar();
        if (v) errs() << "value: " << *n->getUniqueScalar() << "\n";
        else errs() << "no unique scalar\n";);

    // skip nodes that are not read/written by the callee
    if (!isRead(n, CF) && !isModified(n, CF))
      continue;

    // TODO: This must be done for every possible offset of the caller
    // node,
    // TODO: not just for offset 0

    assert(n);
    dsa::Cell callerC = simMap.get(dsa::Cell(const_cast<dsa::Node *>(n), 0));
    assert(!callerC.isNull() && "Not found node in the simulation map");

    AllocaInst *v = getShadowForField(callerC);
    unsigned id = getFieldId(callerC);

    // -- read only node ignore nodes that are only reachable
    // -- from the return of the function
    if (isRead(n, CF) && !isModified(n, CF) && retReach.count(n) <= 0) {
      mkArgRef(*m_B, callerC, idx);
    }
    // -- read/write or new node
    else if (isModified(n, CF)) {
      // -- n is new node iff it is reachable only from the return node
      Constant *argFn = retReach.count(n) ? m_argNewFn : m_argModFn;
      mkArgNewMod(*m_B, argFn, callerC, idx);
    }
    idx++;
  }
}

void ShadowDsaImpl::visitCalloc(CallSite &CS) {
  if (!m_graph->hasCell(*CS.getInstruction()))
    return;
  const dsa::Cell &c = m_graph->getCell(*CS.getInstruction());
  if (c.isNull())
    return;

  if (c.getOffset() == 0) {
    m_B->SetInsertPoint(CS.getInstruction());
    mkShadowStore(*m_B, c);
  } else {
    // TODO: handle multiple nodes
    WARN << "skipping calloc instrumentation because cell "
            "offset is not zero\n";
  }
}

void ShadowDsaImpl::visitAllocationFn(CallSite &CS) {
  if (!m_graph->hasCell(*CS.getInstruction()))
    return;
  const dsa::Cell &c = m_graph->getCell(*CS.getInstruction());
  if (c.isNull())
    return;

  m_B->SetInsertPoint(CS.getInstruction());
  mkShadowLoad(*m_B, c);
}
void ShadowDsaImpl::visitMemSetInst(MemSetInst &I) {
  Value &dst = *(I.getDest());

  if (!m_graph->hasCell(dst))
    return;
  const dsa::Cell &c = m_graph->getCell(dst);
  if (c.isNull())
    return;

  if (c.getOffset() == 0) {
    m_B->SetInsertPoint(&I);
    mkShadowStore(*m_B, c);
  }
}
void ShadowDsaImpl::visitMemTransferInst(MemTransferInst &I) {
  Value &dst = *(I.getDest());
  Value &src = *(I.getSource());

  if (!m_graph->hasCell(dst))
    return;
  if (!m_graph->hasCell(src))
    return;
  const dsa::Cell &dstC = m_graph->getCell(dst);
  const dsa::Cell &srcC = m_graph->getCell(src);
  if (dstC.isNull())
    return;
  // XXX don't remember why this check is needed
  if (dstC.getOffset() != 0)
    return;

  m_B->SetInsertPoint(&I);
  mkShadowMemTrsfr(*m_B, dstC, srcC);
}

void ShadowDsaImpl::mkShadowFunctions(Module &M) {
  LLVMContext &ctx = M.getContext();
  m_Int32Ty = Type::getInt32Ty(ctx);
  Type *i8PtrTy = Type::getInt8PtrTy(ctx);
  Type *voidTy = Type::getVoidTy(ctx);

  m_memLoadFn = M.getOrInsertFunction("shadow.mem.load", voidTy, m_Int32Ty,
                                      m_Int32Ty, i8PtrTy);

  m_memTrsfrLoadFn = M.getOrInsertFunction("shadow.mem.trsfr.load", voidTy,
                                           m_Int32Ty, m_Int32Ty, i8PtrTy);

  m_memStoreFn = M.getOrInsertFunction("shadow.mem.store", m_Int32Ty, m_Int32Ty,
                                       m_Int32Ty, i8PtrTy);

  m_memGlobalVarInitFn = M.getOrInsertFunction(
      "shadow.mem.global.init", m_Int32Ty, m_Int32Ty, m_Int32Ty, i8PtrTy);

  m_memShadowInitFn =
      M.getOrInsertFunction("shadow.mem.init", m_Int32Ty, m_Int32Ty, i8PtrTy);

  m_memShadowArgInitFn = M.getOrInsertFunction("shadow.mem.arg.init", m_Int32Ty,
                                               m_Int32Ty, i8PtrTy);

  m_argRefFn = M.getOrInsertFunction("shadow.mem.arg.ref", voidTy, m_Int32Ty,
                                     m_Int32Ty, m_Int32Ty, i8PtrTy);

  m_argModFn = M.getOrInsertFunction("shadow.mem.arg.mod", m_Int32Ty, m_Int32Ty,
                                     m_Int32Ty, m_Int32Ty, i8PtrTy);
  m_argNewFn = M.getOrInsertFunction("shadow.mem.arg.new", m_Int32Ty, m_Int32Ty,
                                     m_Int32Ty, m_Int32Ty, i8PtrTy);

  m_markIn = M.getOrInsertFunction("shadow.mem.in", voidTy, m_Int32Ty,
                                   m_Int32Ty, m_Int32Ty, i8PtrTy);
  m_markOut = M.getOrInsertFunction("shadow.mem.out", voidTy, m_Int32Ty,
                                    m_Int32Ty, m_Int32Ty, i8PtrTy);
}

void ShadowDsaImpl::doReadMod() {
  if (!m_callGraph) {
    WARN << "Call graph is missing. Not computing local mod/ref.";
    return;
  }

  // for every scc in bottom-up order
  for (auto it = scc_begin(m_callGraph); !it.isAtEnd(); ++it) {
    NodeSet read;
    const std::vector<CallGraphNode *> &scc = *it;
    NodeSet modified;

    // compute read/mod, sharing information between scc
    for (CallGraphNode *cgn : scc) {
      Function *f = cgn->getFunction();
      if (!f)
        continue;
      updateReadMod(*f, read, modified);
    }

    // set the computed read/mod to all functions in the scc
    for (CallGraphNode *cgn : scc) {
      Function *f = cgn->getFunction();
      if (!f)
        continue;
      m_readList[f].insert(read.begin(), read.end());
      m_modList[f].insert(modified.begin(), modified.end());
    }
  }
}

void ShadowDsaImpl::updateReadMod(Function &F, NodeSet &readSet,
                                  NodeSet &modSet) {
  if (!m_dsa.hasGraph(F))
    return;

  dsa::Graph &G = m_dsa.getGraph(F);
  for (Instruction &inst : llvm::instructions(F)) {
    if (auto *li = dyn_cast<LoadInst>(&inst)) {
      if (G.hasCell(*(li->getPointerOperand()))) {
        const dsa::Cell &c = G.getCell(*(li->getPointerOperand()));
        if (!c.isNull())
          readSet.insert(c.getNode());
      }
    } else if (auto *si = dyn_cast<StoreInst>(&inst)) {
      if (G.hasCell(*(si->getPointerOperand()))) {
        const dsa::Cell &c = G.getCell(*(si->getPointerOperand()));
        if (!c.isNull())
          modSet.insert(c.getNode());
      }
    } else if (auto *ci = dyn_cast<CallInst>(&inst)) {
      CallSite CS(ci);
      Function *cf = CS.getCalledFunction();

      if (!cf)
        continue;
      if (cf->getName().equals("calloc")) {
        const dsa::Cell &c = G.getCell(inst);
        if (!c.isNull())
          modSet.insert(c.getNode());
      } else if (m_dsa.hasGraph(*cf)) {
        assert(&(m_dsa.getGraph(*cf)) == &G &&
               "Computing local mod/ref in context sensitive mode");
        readSet.insert(m_readList[cf].begin(), m_readList[cf].end());
        modSet.insert(m_modList[cf].begin(), m_modList[cf].end());
      }
    }
    // TODO: handle intrinsics (memset,memcpy) and other library functions
  }
}
} // namespace

namespace seahorn {

bool ShadowMemSeaDsa::runOnModule(llvm::Module &M) {
  if (M.begin() == M.end())
    return false;

  dsa::GlobalAnalysis &dsa = getAnalysis<dsa::DsaAnalysis>().getDsaAnalysis();
  TargetLibraryInfo *tli = nullptr;
  auto tliPass = getAnalysisIfAvailable<TargetLibraryInfoWrapperPass>();
  if (tliPass)
    tli = &tliPass->getTLI();

  CallGraph *cg = nullptr;
  auto cgPass = getAnalysisIfAvailable<CallGraphWrapperPass>();
  if (cgPass)
    cg = &cgPass->getCallGraph();

  LOG("shadow_verbose", errs() << "Module before shadow insertion:\n"
                               << M << "\n";);

  ShadowDsaImpl impl(dsa, tli, cg, *this, SplitFields, LocalReadMod);
  bool res = impl.runOnModule(M);
  LOG("shadow_verbose", errs() << "Module after shadow insertion:\n"
                               << M << "\n";);

  // -- verifyModule returns true if module is broken
  assert(!llvm::verifyModule(M, &errs()));
  return res;
}

void ShadowMemSeaDsa::getAnalysisUsage(llvm::AnalysisUsage &AU) const {
  AU.setPreservesAll();
  AU.addRequiredTransitive<dsa::DsaAnalysis>();
  AU.addRequired<llvm::CallGraphWrapperPass>();
  AU.addRequired<llvm::DominatorTreeWrapperPass>();
  AU.addRequired<llvm::AssumptionCacheTracker>();
}

class StripShadowMem : public ModulePass {
public:
  static char ID;
  StripShadowMem() : ModulePass(ID) {}

  virtual StringRef getPassName() const { return "StripShadowMem"; }

  virtual void getAnalysisUsage(AnalysisUsage &AU) const override {
    AU.setPreservesAll();
  }

  virtual bool runOnModule(Module &M) override {
    std::vector<std::string> voidFnNames = {"shadow.mem.load",
                                            "shadow.mem.arg.ref",
                                            "shadow.mem.in", "shadow.mem.out"};

    for (auto &name : voidFnNames) {
      Function *fn = M.getFunction(name);
      if (!fn)
        continue;

      while (!fn->use_empty()) {
        CallInst *ci = cast<CallInst>(fn->user_back());
        Value *last = ci->getArgOperand(ci->getNumArgOperands() - 1);
        ci->eraseFromParent();
        seahorn::RecursivelyDeleteTriviallyDeadInstructions(last);
      }
    }

    std::vector<std::string> intFnNames = {
        "shadow.mem.store", "shadow.mem.init", "shadow.mem.arg.init",
        "shadow.mem.arg.mod"};
    Value *zero = ConstantInt::get(Type::getInt32Ty(M.getContext()), 0);

    for (auto &name : intFnNames) {
      Function *fn = M.getFunction(name);
      if (!fn)
        continue;

      while (!fn->use_empty()) {
        CallInst *ci = cast<CallInst>(fn->user_back());
        Value *last = ci->getArgOperand(ci->getNumArgOperands() - 1);
        ci->replaceAllUsesWith(zero);
        ci->eraseFromParent();
        seahorn::RecursivelyDeleteTriviallyDeadInstructions(last);
      }
    }

    return true;
  }
};
} // namespace seahorn

namespace seahorn {
bool isShadowMemInst(const llvm::Value &v) {
  if (auto *inst = dyn_cast<const Instruction>(&v)) {
    return inst->getMetadata("shadow.mem");
  }
  return false;
}

char ShadowMemSeaDsa::ID = 0;
char StripShadowMem::ID = 0;
Pass *createStripShadowMemPass() { return new StripShadowMem(); }
#ifdef USE_NEW_SHADOW_SEA_DSA
Pass *createShadowMemSeaDsaPass() { return new ShadowMemSeaDsa(); }
#endif
} // namespace seahorn

static llvm::RegisterPass<seahorn::StripShadowMem>
    Y("strip-shadow-dsa", "Remove shadow.mem pseudo-functions");
