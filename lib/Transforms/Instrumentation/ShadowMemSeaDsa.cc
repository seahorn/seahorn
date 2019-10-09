#include "seahorn/Transforms/Instrumentation/ShadowMemSeaDsa.hh"
#include "llvm/ADT/SCCIterator.h"
#include "llvm/ADT/STLExtras.h"
#include "llvm/Analysis/AssumptionCache.h"
#include "llvm/Analysis/BasicAliasAnalysis.h"
#include "llvm/Analysis/CallGraph.h"
#include "llvm/Analysis/MemoryBuiltins.h"
#include "llvm/Analysis/TargetLibraryInfo.h"
#include "llvm/Analysis/TypeBasedAliasAnalysis.h"
#include "llvm/IR/DataLayout.h"
#include "llvm/IR/Dominators.h"
#include "llvm/IR/IRBuilder.h"
#include "llvm/IR/InstIterator.h"
#include "llvm/IR/IntrinsicInst.h"
#include "llvm/IR/Verifier.h"
#include "llvm/Support/raw_ostream.h"
#include "llvm/Transforms/Utils/BasicBlockUtils.h"
#include "llvm/Transforms/Utils/PromoteMemToReg.h"

#include "boost/range/algorithm/set_algorithm.hpp"

#include "sea_dsa/AllocSiteInfo.hh"
#include "sea_dsa/CallSite.hh"
#include "sea_dsa/DsaAnalysis.hh"
#include "sea_dsa/Mapper.hh"
#include "sea_dsa/TypeUtils.hh"
#include "seahorn/Support/SeaDebug.h"
#include "seahorn/Support/SeaLog.hh"
#include "seahorn/Support/SortTopo.hh"
#include "seahorn/Transforms/Utils/Local.hh"

llvm::cl::opt<bool> SplitFields("horn-sea-dsa-split",
                                llvm::cl::desc("DSA: Split nodes by fields"),
                                llvm::cl::init(false));

llvm::cl::opt<bool>
    LocalReadMod("horn-sea-dsa-local-mod",
                 llvm::cl::desc("DSA: Compute read/mod info locally"),
                 llvm::cl::init(false));

llvm::cl::opt<bool> ShadowMemOptimize(
    "horn-shadow-mem-optimize",
    llvm::cl::desc("Use the solved form for ShadowMem (MemSSA)"),
    llvm::cl::init(true));

llvm::cl::opt<bool>
    ShadowMemUseTBAA("horn-shadow-mem-use-tbaa",
                     llvm::cl::desc("Use TypeBasedAA in the MemSSA optimizer"),
                     llvm::cl::init(true));

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
    if (auto *gv = dyn_cast_or_null<GlobalVariable>(v))
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
    for (const auto &edg : n->links())
      markReachableNodes(edg.second->getNode(), set);
}

template <typename Set>
void reachableNodes(const Function &fn, dsa::Graph &g, Set &inputReach,
                    Set &retReach) {
  // formal parameters
  for (const auto &formal : fn.args())
    if (g.hasCell(formal)) {
      dsa::Cell &c = g.mkCell(formal, dsa::Cell());
      markReachableNodes(c.getNode(), inputReach);
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

/// Interface used to query BasicAA and TBAA, if available. This should ideally
/// be replaced with llvm::AAResultsWrapperPass, but we hit crashes when calling
/// alias -- this class is just a simple workaround.
/// TODO: Investigate crashes in llvm::AAResultsWrapperPass.
class LocalAAResultsWrapper {
  llvm::BasicAAResult *m_baa = nullptr;
  llvm::TypeBasedAAResult *m_tbaa = nullptr;

  MemoryLocation getMemLoc(Value &ptr, Value *inst, Optional<unsigned> size) {
    MemoryLocation loc(&ptr);
    if (auto *i = dyn_cast_or_null<Instruction>(inst)) {
      AAMDNodes aaTags;
      i->getAAMetadata(aaTags);
      loc = MemoryLocation(&ptr, MemoryLocation::UnknownSize, aaTags);
    }

    if (size.hasValue())
      loc = loc.getWithNewSize(*size);

    return loc;
  }

public:
  LocalAAResultsWrapper() = default;
  LocalAAResultsWrapper(BasicAAResult *baa, TypeBasedAAResult *tbaa)
      : m_baa(baa), m_tbaa(tbaa) {}
  LocalAAResultsWrapper(const LocalAAResultsWrapper &) = default;
  LocalAAResultsWrapper &operator=(const LocalAAResultsWrapper &) = default;

  bool isNoAlias(Value &ptrA, Value *instA, Optional<unsigned> sizeA,
                 Value &ptrB, Value *instB, Optional<unsigned> sizeB) {
    if (!m_baa && !m_tbaa)
      return false;

    MemoryLocation A = getMemLoc(ptrA, instA, sizeA);
    MemoryLocation B = getMemLoc(ptrB, instB, sizeB);

    if (m_tbaa && m_tbaa->alias(A, B) == AliasResult::NoAlias)
      return true;

    return m_baa && m_baa->alias(A, B) == AliasResult::NoAlias;
  }
};

class ShadowDsaImpl : public InstVisitor<ShadowDsaImpl> {
  dsa::GlobalAnalysis &m_dsa;
  dsa::AllocSiteInfo &m_asi;
  TargetLibraryInfo &m_tli;
  const DataLayout *m_dl;
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

  llvm::SmallVector<llvm::Constant *, 5> m_memInitFunctions;

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
  dsa::Graph *m_graph = nullptr;
  LocalAAResultsWrapper m_localAAResults;

  // Associate shadow and concrete instructions, used by the memUse solver.
  // Alternatively, this could be implemented by walking instructions forward,
  // starting from a shadow instructions, until the first concrete instructions
  // is found, or by using some metadata.
  llvm::DenseMap<CallInst *, Value *> m_shadowOpToAccessedPtr;
  llvm::DenseMap<CallInst *, Value *> m_shadowOpToConcreteInst;
  void associateConcretePtr(CallInst &memOp, Value &ptr, Value *inst);
  Value *getAssociatedConcretePtr(CallInst &memOp);
  Value *getAssociatedConcreteInst(CallInst &memOp);

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
      ++m_maxId;
      return id;
    }

    // -- allocate enough ids for the node and all its fields
    m_maxId += n.size();
    return id + offset;
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

  MDNode *mkMetaConstant(llvm::Optional<unsigned> val) {
    assert(m_llvmCtx);
    if (val.hasValue())
      return MDNode::get(*m_llvmCtx,
                         ConstantAsMetadata::get(ConstantInt::get(
                             *m_llvmCtx, llvm::APInt(64u, size_t(*val)))));

    return MDNode::get(*m_llvmCtx, llvm::None);
  }

  Optional<unsigned> maybeGetMetaConstant(CallInst &memOp, StringRef metaName) {
    if (MDNode *meta = memOp.getMetadata(metaName))
      if (meta->getNumOperands() > 0)
        if (auto *c = dyn_cast<ConstantAsMetadata>(meta->getOperand(0)))
          if (auto *cInt = dyn_cast<ConstantInt>(c->getValue()))
            return unsigned(cInt->getLimitedValue());

    return llvm::None;
  }

  void markDefCall(CallInst *ci, llvm::Optional<unsigned> accessedBytes) {
    assert(m_llvmCtx);
    MDNode *meta = MDNode::get(*m_llvmCtx, None);
    ci->setMetadata(m_metadataTag, meta);
    ci->setMetadata(m_memDefTag, mkMetaConstant(accessedBytes));
  }

  void markUseCall(CallInst *ci, llvm::Optional<unsigned> accessedBytes) {
    assert(m_llvmCtx);
    Module *m = ci->getModule();
    MDNode *meta = MDNode::get(*m_llvmCtx, None);
    ci->setMetadata(m_metadataTag, meta);
    ci->setMetadata(m_memUseTag, mkMetaConstant(accessedBytes));
  }

  CallInst &mkShadowAllocInit(IRBuilder<> &B, Constant *fn, AllocaInst *a,
                              const dsa::Cell &c) {
    B.Insert(a, "shadow.mem." + Twine(getFieldId(c)));
    CallInst *ci;
    Value *us = getUniqueScalar(*m_llvmCtx, B, c);
    ci = B.CreateCall(fn, {B.getInt32(getFieldId(c)), us}, "sm");
    markDefCall(ci, llvm::None);
    B.CreateStore(ci, a);
    return *ci;
  }

  CallInst &mkShadowStore(IRBuilder<> &B, const dsa::Cell &c,
                          llvm::Optional<unsigned> bytes) {
    AllocaInst *v = getShadowForField(c);
    auto &ci = mkStoreFnCall(B, c, v, bytes);
    B.CreateStore(&ci, v);
    return ci;
  }

  CallInst &mkStoreFnCall(IRBuilder<> &B, const dsa::Cell &c, AllocaInst *v,
                          llvm::Optional<unsigned> bytes) {
    auto *ci = B.CreateCall(m_memStoreFn,
                            {m_B->getInt32(getFieldId(c)), m_B->CreateLoad(v),
                             getUniqueScalar(*m_llvmCtx, B, c)},
                            "sm");
    markDefCall(ci, bytes);
    return *ci;
  }

  CallInst *mkShadowGlobalVarInit(IRBuilder<> &B, const dsa::Cell &c,
                                  llvm::GlobalVariable &_u,
                                  llvm::Optional<unsigned> bytes) {

    // Do not insert shadow.mem.global.init() if the global is a unique scalar
    // Such scalars are initialized directly in the code
    Value *scalar = getUniqueScalar(*m_llvmCtx, B, c);
    if (!isa<ConstantPointerNull>(scalar))
      return nullptr;

    Value *u = B.CreateBitCast(&_u, Type::getInt8PtrTy(*m_llvmCtx));
    AllocaInst *v = getShadowForField(c);
    auto *ci = B.CreateCall(
        m_memGlobalVarInitFn,
        {m_B->getInt32(getFieldId(c)), m_B->CreateLoad(v), u}, "sm");
    markDefCall(ci, bytes);
    B.CreateStore(ci, v);
    return ci;
  }

  CallInst &mkShadowLoad(IRBuilder<> &B, const dsa::Cell &c,
                         llvm::Optional<unsigned> bytes) {
    auto *ci = B.CreateCall(m_memLoadFn, {B.getInt32(getFieldId(c)),
                                          B.CreateLoad(getShadowForField(c)),
                                          getUniqueScalar(*m_llvmCtx, B, c)});
    markUseCall(ci, bytes);
    return *ci;
  }

  std::pair<CallInst &, CallInst &>
  mkShadowMemTrsfr(IRBuilder<> &B, const dsa::Cell &dst, const dsa::Cell &src,
                   llvm::Optional<unsigned> bytes) {
    // insert memtrfr.load for the read access
    auto *loadCI =
        B.CreateCall(m_memTrsfrLoadFn, {B.getInt32(getFieldId(src)),
                                        B.CreateLoad(getShadowForField(src)),
                                        getUniqueScalar(*m_llvmCtx, B, src)});
    markUseCall(loadCI, bytes);

    // insert normal mem.store for the write access
    auto &storeCI = mkShadowStore(B, dst, bytes);
    return {*loadCI, storeCI};
  }

  CallInst &mkArgRef(IRBuilder<> &B, const dsa::Cell &c, unsigned idx,
                     llvm::Optional<unsigned> bytes) {
    AllocaInst *v = getShadowForField(c);
    unsigned id = getFieldId(c);
    auto *ci = B.CreateCall(m_argRefFn, {B.getInt32(id), m_B->CreateLoad(v),
                                         m_B->getInt32(idx),
                                         getUniqueScalar(*m_llvmCtx, B, c)});
    markUseCall(ci, bytes);
    return *ci;
  }

  CallInst &mkArgNewMod(IRBuilder<> &B, Constant *argFn, const dsa::Cell &c,
                        unsigned idx, llvm::Optional<unsigned> bytes) {
    AllocaInst *v = getShadowForField(c);
    unsigned id = getFieldId(c);
    auto *ci = B.CreateCall(argFn,
                            {B.getInt32(id), B.CreateLoad(v), B.getInt32(idx),
                             getUniqueScalar(*m_llvmCtx, B, c)},
                            "sh");
    B.CreateStore(ci, v);
    markDefCall(ci, bytes);
    return *ci;
  }

  CallInst &mkMarkIn(IRBuilder<> &B, const dsa::Cell &c, Value *v, unsigned idx,
                     llvm::Optional<unsigned> bytes) {
    auto *ci =
        B.CreateCall(m_markIn, {B.getInt32(getFieldId(c)), v, B.getInt32(idx),
                                getUniqueScalar(*m_llvmCtx, B, c)});
    markDefCall(ci, bytes);
    return *ci;
  }

  CallInst &mkMarkOut(IRBuilder<> &B, const dsa::Cell &c, unsigned idx,
                      llvm::Optional<unsigned> bytes) {
    auto *ci = B.CreateCall(m_markOut, {B.getInt32(getFieldId(c)),
                                        B.CreateLoad(getShadowForField(c)),
                                        B.getInt32(idx),
                                        getUniqueScalar(*m_llvmCtx, B, c)});
    markUseCall(ci, bytes);
    return *ci;
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
    // for every bb in topological order
    for (auto *bb : llvm::inverse_post_order(&F.getEntryBlock())) {
      // for every PHINode
      for (auto &phi : bb->phis()) {
        // for every incoming value
        for (auto &val : phi.incoming_values()) {
          // if an incoming value has metadata, take it, and be done
          if (auto *inst = dyn_cast<Instruction>(&val)) {
            if (auto *meta = inst->getMetadata(m_metadataTag)) {
              phi.setMetadata(m_metadataTag, meta);
              phi.setMetadata(m_memPhiTag, meta);
              break;
            }
          }
        }
      }
    }
  }

  /// \brief Put memUses (shadow loads, etc.,) into a solved form. This
  /// optimizes loads to use the most recent non-clobbering defs. Not that this
  /// is an optimization over the existing Memory SSA form.
  void solveUses(Function &F);

  // Helper functions used by `solveUses`.
  using MaybeAllocSites = Optional<SmallDenseSet<Value *, 8>>;
  using AllocSitesCache = DenseMap<Value *, MaybeAllocSites>;
  bool isMemInit(const CallInst &memOp);
  CallInst &getParentDef(CallInst &memOp);
  const MaybeAllocSites &getAllAllocSites(Value &ptr, AllocSitesCache &cache);
  bool mayClobber(CallInst &memDef, CallInst &memUse, AllocSitesCache &cache);

public:
  ShadowDsaImpl(dsa::GlobalAnalysis &dsa, dsa::AllocSiteInfo &asi,
                TargetLibraryInfo &tli, CallGraph *cg, Pass &pass,
                bool splitDsaNodes = false, bool computeReadMod = false)
      : m_dsa(dsa), m_asi(asi), m_tli(tli), m_dl(nullptr), m_callGraph(cg),
        m_pass(pass), m_splitDsaNodes(splitDsaNodes),
        m_computeReadMod(computeReadMod) {}

  bool runOnModule(Module &M) {
    m_dl = &M.getDataLayout();

    if (m_computeReadMod)
      doReadMod();

    mkShadowFunctions(M);
    m_nodeIds.clear();

    bool changed = false;
    for (Function &F : M)
      changed |= runOnFunction(F);
    return changed;
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

  const llvm::StringRef m_metadataTag = "shadow.mem";
  const llvm::StringRef m_memDefTag = "shadow.mem.def";
  const llvm::StringRef m_memUseTag = "shadow.mem.use";
  const llvm::StringRef m_memPhiTag = "shadow.mem.phi";
};

bool ShadowDsaImpl::runOnFunction(Function &F) {
  if (F.isDeclaration())
    return false;

  if (!m_dsa.hasGraph(F))
    return false;

  m_graph = &m_dsa.getGraph(F);
  m_shadows.clear();

  // Alias analyses in LLVM are function passes, so we can only get the results
  // once the function is known. The Pass Manager is not able to schedule the
  // AA's here, construct them manually as a workaround.
  AAResults results(m_tli);
  DominatorTree &dt =
      m_pass.getAnalysis<llvm::DominatorTreeWrapperPass>(F).getDomTree();
  AssumptionCache &ac =
      m_pass.getAnalysis<llvm::AssumptionCacheTracker>().getAssumptionCache(F);
  BasicAAResult baa(*m_dl, m_tli, ac, &dt);
  // AA's need to be registered in the results object that will finish their
  // initialization.
  results.addAAResult(baa);

  std::unique_ptr<TypeBasedAAResult> tbaa = nullptr;
  if (ShadowMemUseTBAA) {
    tbaa = llvm::make_unique<TypeBasedAAResult>();
    results.addAAResult(*tbaa);
  }

  m_localAAResults = LocalAAResultsWrapper(&baa, tbaa.get());

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
  for (const auto &nodeToShadow : m_shadows) {
    const dsa::Node *n = nodeToShadow.first;

    Constant *fn =
        reach.count(n) <= 0 ? m_memShadowInitFn : m_memShadowArgInitFn;

    for (auto jt : nodeToShadow.second) {
      dsa::Cell c(const_cast<dsa::Node *>(n), jt.first);
      AllocaInst *a = jt.second;
      inits[c.getNode()][getOffset(c)] = &mkShadowAllocInit(B, fn, a, c);
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
      mkMarkIn(B, c, inits[n][0], idx, llvm::None);
    }

    if (isModified(n, F)) {
      assert(!inits[n].empty());
      /// final value
      mkMarkOut(B, c, idx, llvm::None);
    }
    ++idx;
  }

  // -- convert new allocas to registers
  runMem2Reg(F);
  // -- infer types for PHINodes
  inferTypeOfPHINodes(F);

  if (ShadowMemOptimize)
    solveUses(F);

  m_B.reset(nullptr);
  m_llvmCtx = nullptr;
  m_graph = nullptr;
  m_shadows.clear();
  m_shadowOpToAccessedPtr.clear();
  m_shadowOpToConcreteInst.clear();

  return true;
}

void ShadowDsaImpl::visitFunction(Function &fn) {
  if (fn.getName().equals("main")) {
    visitMainFunction(fn);
  }
}

void ShadowDsaImpl::visitMainFunction(Function &fn) {
  // set insertion point to the beginning of the main function
  m_B->SetInsertPoint(&*fn.getEntryBlock().begin());

  // iterate over all globals
  for (auto &gv : fn.getParent()->globals()) {
    // skip globals that are used internally by llvm
    if (gv.getSection().equals("llvm.metadata"))
      continue;
    // skip globals that do not appear in alias analysis
    if (!m_graph->hasCell(gv))
      continue;
    // insert call to mkShadowGlobalVarInit()
    auto sz = dsa::getTypeSizeInBytes(*gv.getValueType(), *m_dl);
    if (CallInst *memInit =
            mkShadowGlobalVarInit(*m_B, m_graph->getCell(gv), gv, sz))
      associateConcretePtr(*memInit, gv, nullptr);
  }
}

void ShadowDsaImpl::visitAllocaInst(AllocaInst &I) {
  if (!m_graph->hasCell(I))
    return;

  const dsa::Cell &c = m_graph->getCell(I);
  if (c.isNull())
    return;

  assert(dsa::AllocSiteInfo::isAllocSite(I));

  m_B->SetInsertPoint(&I);
  CallInst &memUse =
      mkShadowLoad(*m_B, c, dsa::AllocSiteInfo::getAllocSiteSize(I));
  associateConcretePtr(memUse, I, &I);
}

void ShadowDsaImpl::visitLoadInst(LoadInst &I) {
  Value *loadSrc = I.getPointerOperand();

  if (!m_graph->hasCell(*loadSrc))
    return;
  const dsa::Cell &c = m_graph->getCell(*loadSrc);
  if (c.isNull())
    return;

  m_B->SetInsertPoint(&I);
  CallInst &memUse =
      mkShadowLoad(*m_B, c, dsa::getTypeSizeInBytes(*I.getType(), *m_dl));
  associateConcretePtr(memUse, *loadSrc, &I);
}

void ShadowDsaImpl::visitStoreInst(StoreInst &I) {
  Value *storeDst = I.getPointerOperand();
  if (!m_graph->hasCell(*storeDst))
    return;
  const dsa::Cell &c = m_graph->getCell(*storeDst);
  if (c.isNull())
    return;

  m_B->SetInsertPoint(&I);
  CallInst &memDef = mkShadowStore(
      *m_B, c, dsa::getTypeSizeInBytes(*I.getValueOperand()->getType(), *m_dl));
  associateConcretePtr(memDef, *storeDst, &I);
}

void ShadowDsaImpl::visitCallSite(CallSite CS) {
  if (CS.isIndirectCall())
    return;

  auto *callee = CS.getCalledFunction();
  if (!callee)
    return;

  if ((callee->getName().startswith("seahorn.") ||
       callee->getName().startswith("verifier.")) &&
      /* seahorn.bounce should be treated as a regular function*/
      !(callee->getName().startswith("seahorn.bounce")))
    return;

  auto *callInst = CS.getInstruction();

  LOG("shadow_cs", errs() << "Call: " << *callInst << "\n";);

  if (callee->getName().equals("calloc")) {
    visitCalloc(CS);
    return;
  }

  if (dsa::AllocSiteInfo::isAllocSite(*callInst)) {
    visitAllocationFn(CS);
    return;
  }

  if (m_dsa.hasGraph(*callee)) {
    ImmutableCallSite ics(callInst);
    dsa::DsaCallSite dcs(ics);
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
      mkArgRef(*m_B, callerC, idx, llvm::None);
      // Unclear how to get the associated concrete pointer here.
    }
    // -- read/write or new node
    else if (isModified(n, CF)) {
      // -- n is new node iff it is reachable only from the return node
      Constant *argFn = retReach.count(n) ? m_argNewFn : m_argModFn;
      mkArgNewMod(*m_B, argFn, callerC, idx, llvm::None);
      // Unclear how to get the associated concrete pointer here.
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

  auto &callInst = *CS.getInstruction();
  assert(dsa::AllocSiteInfo::isAllocSite(callInst));

  if (c.getOffset() == 0) {
    m_B->SetInsertPoint(&callInst);
    CallInst &memDef =
        mkShadowStore(*m_B, c, dsa::AllocSiteInfo::getAllocSiteSize(callInst));
    associateConcretePtr(memDef, callInst, &callInst);
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

  auto &callInst = *CS.getInstruction();
  m_B->SetInsertPoint(&callInst);

  CallInst &memUse =
      mkShadowLoad(*m_B, c, dsa::AllocSiteInfo::getAllocSiteSize(callInst));
  assert(dsa::AllocSiteInfo::isAllocSite(callInst));
  associateConcretePtr(memUse, callInst, &callInst);
}

void ShadowDsaImpl::visitMemSetInst(MemSetInst &I) {
  LOG("dsa.memset", errs() << "Visitng memset: " << I << "\n";);
  Value &dst = *(I.getDest());

  if (!m_graph->hasCell(dst)) {
    LOG("dsa.memset", errs() << "No DSA cell for " << dst << "\n";);
    return;
  }
  const dsa::Cell &c = m_graph->getCell(dst);
  if (c.isNull()) {
    LOG("dsa.memset", errs() << "Dst cell is null\n";);
    return;
  }

  // XXX: Don't remember why this check was needed. Disabling for now.
  // if (c.getOffset() != 0) return;
  m_B->SetInsertPoint(&I);

  Optional<unsigned> len = llvm::None;
  if (auto *sz = dyn_cast_or_null<ConstantInt>(I.getLength()))
    len = sz->getLimitedValue();

  CallInst &memDef = mkShadowStore(*m_B, c, len);
  associateConcretePtr(memDef, dst, &I);
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

  /* 
  // XXX don't remember why this check is needed
  if (dstC.getOffset() != 0)
    return;
  */
  Optional<unsigned> len = llvm::None;
  if (auto *length = dyn_cast_or_null<ConstantInt>(I.getLength()))
    len = length->getLimitedValue();

  m_B->SetInsertPoint(&I);
  auto useDefPair = mkShadowMemTrsfr(*m_B, dstC, srcC, len);
  associateConcretePtr(useDefPair.first, src, &I);
  associateConcretePtr(useDefPair.second, dst, &I);
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

  m_memInitFunctions = {m_memShadowInitFn, m_memGlobalVarInitFn,
                        m_memShadowArgInitFn, m_memShadowUniqArgInitFn,
                        m_memShadowUniqInitFn};
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

void ShadowDsaImpl::associateConcretePtr(CallInst &memOp, Value &ptr,
                                         Value *inst) {
  assert(memOp.getMetadata(m_metadataTag));
  if (auto *i = dyn_cast<Instruction>(&ptr))
    assert(!i->getMetadata(m_metadataTag));
  if (auto *i = dyn_cast_or_null<Instruction>(inst))
    assert(!i->getMetadata(m_metadataTag));

  m_shadowOpToAccessedPtr.insert({&memOp, &ptr});
  if (inst)
    m_shadowOpToConcreteInst.insert({&memOp, inst});
}

Value *ShadowDsaImpl::getAssociatedConcretePtr(CallInst &memOp) {
  assert(memOp.getMetadata(m_metadataTag));
  auto it = m_shadowOpToAccessedPtr.find(&memOp);
  if (it != m_shadowOpToAccessedPtr.end())
    return it->second;

  return nullptr;
}

Value *ShadowDsaImpl::getAssociatedConcreteInst(CallInst &memOp) {
  assert(memOp.getMetadata(m_metadataTag));
  auto it = m_shadowOpToConcreteInst.find(&memOp);
  if (it != m_shadowOpToConcreteInst.end())
    return it->second;

  return nullptr;
}

bool ShadowDsaImpl::isMemInit(const CallInst &memOp) {
  assert(memOp.getMetadata(m_metadataTag));
  auto *fn = memOp.getCalledFunction();
  assert(fn);
  return llvm::is_contained(m_memInitFunctions, fn);
}

CallInst &ShadowDsaImpl::getParentDef(CallInst &memOp) {
  assert(memOp.getMetadata(m_metadataTag));

  if (isMemInit(memOp))
    return memOp;

  auto *fn = memOp.getCalledFunction();
  assert(fn);
  assert(fn == m_memLoadFn || fn == m_memStoreFn || fn == m_memTrsfrLoadFn);

  assert(memOp.getNumOperands() >= 1);
  Value *defArg = memOp.getOperand(1);
  assert(defArg);
  assert(isa<CallInst>(defArg));
  auto *def = cast<CallInst>(defArg);
  assert(def->getMetadata(m_memDefTag));

  return *def;
}

const ShadowDsaImpl::MaybeAllocSites &
ShadowDsaImpl::getAllAllocSites(Value &ptr, AllocSitesCache &cache) {
  // Performs a simple walk over use-def chains until it finds all allocation
  // sites or an instruction it cannot look thru (e.g., a load).
  assert(ptr.getType()->isPointerTy());

  auto *strippedInit = ptr.stripPointerCastsAndBarriers();
  {
    auto it = cache.find(strippedInit);
    if (it != cache.end())
      return it->second;
  }

  SmallDenseSet<Value *, 8> allocSites;
  DenseSet<Value *> visited;
  SmallVector<Value *, 8> worklist = {strippedInit};

  while (!worklist.empty()) {
    Value *current = worklist.pop_back_val();
    assert(current);
    Value *stripped = current->stripPointerCastsAndBarriers();
    if (visited.count(stripped) > 0)
      continue;

    visited.insert(stripped);
    LOG("shadow_optimizer", llvm::errs() << "Visiting: " << *stripped << "\n");

    if (isa<AllocaInst>(stripped) || isa<Argument>(stripped) ||
        isa<GlobalValue>(stripped)) {
      allocSites.insert(stripped);
      continue;
    }

    // Check with the DSA if a call is considered an allocation site.
    if (auto *ci = dyn_cast<CallInst>(stripped))
      if (m_graph->hasAllocSiteForValue(*ci)) {
        allocSites.insert(stripped);
        continue;
      }

    if (auto *gep = dyn_cast<GetElementPtrInst>(stripped)) {
      worklist.push_back(gep->getPointerOperand());
      continue;
    }

    if (auto *phi = dyn_cast<PHINode>(stripped)) {
      for (Value *v : llvm::reverse(phi->incoming_values()))
        worklist.push_back(v);

      continue;
    }

    if (auto *gamma = dyn_cast<SelectInst>(stripped)) {
      worklist.push_back(gamma->getFalseValue());
      worklist.push_back(gamma->getTrueValue());
      continue;
    }

    LOG("shadow_optimizer",
        llvm::errs() << "Cannot retrieve all alloc sites for " << ptr
                     << "\n\tbecause of the instruction: " << *stripped
                     << "\n");
    return (cache[strippedInit] = llvm::None);
  }

  return (cache[strippedInit] = allocSites);
}

bool ShadowDsaImpl::mayClobber(CallInst &memDef, CallInst &memUse,
                               AllocSitesCache &cache) {
  LOG("shadow_optimizer", llvm::errs() << "\n~~~~\nmayClobber(" << memDef
                                       << ", " << memUse << ")?\n");

  if (isMemInit(memDef))
    return true;

  LOG("shadow_optimizer", llvm::errs() << "\tmayClobber[1]\n");

  // Get the corresponding pointers and check if these two pointers have
  // disjoint allocation sites -- if not, they cannot alias.
  // This can be extended further with offset tracking.

  Value *usePtr = getAssociatedConcretePtr(memUse);
  if (!usePtr)
    return true;

  LOG("shadow_optimizer", llvm::errs() << "\tmayClobber[2 ]\n");

  Value *defPtr = getAssociatedConcretePtr(memDef);
  if (!defPtr)
    return true;

  usePtr = usePtr->stripPointerCastsAndBarriers();
  defPtr = defPtr->stripPointerCastsAndBarriers();
  assert(m_graph->hasCell(*usePtr));
  assert(m_graph->hasCell(*defPtr));

  LOG("shadow_optimizer",
      llvm::errs() << "alias(" << *usePtr << ", " << *defPtr << ")?\n");

  const Optional<unsigned> usedBytes =
      maybeGetMetaConstant(memUse, m_memUseTag);
  const Optional<unsigned> defdBytes =
      maybeGetMetaConstant(memDef, m_memDefTag);

  // If the offsets don't overlap, no clobbering may happen.
  {
    const dsa::Cell &useCell = m_graph->getCell(*usePtr);
    const dsa::Cell &defCell = m_graph->getCell(*defPtr);
    assert(useCell.getNode() == defCell.getNode());
    // This works with arrays in SeaDsa because all array elements share the
    // same abstract field.

    const unsigned useStartOffset = useCell.getOffset();
    const unsigned defStartOffset = defCell.getOffset();
    LOG("shadow_optimizer",
        llvm::errs() << "\tmayClobber[3]\n\tuseStart: " << useStartOffset
                     << "\n\tdefStart: " << defStartOffset << "\n");

    if (defdBytes.hasValue())
      if (useStartOffset >= defStartOffset + *defdBytes)
        return false;

    if (usedBytes.hasValue())
      if (useStartOffset + *usedBytes <= defStartOffset)
        return false;
  }
  LOG("shadow_optimizer", llvm::errs() << "\tmayClobber[4]\n");

  {
    Value *concreteInstUse = getAssociatedConcreteInst(memUse);
    Value *concreteInstDef = getAssociatedConcreteInst(memDef);
    if (m_localAAResults.isNoAlias(*usePtr, concreteInstUse, usedBytes, *defPtr,
                                   concreteInstDef, defdBytes))
      return false;
  }

  LOG("shadow_optimizer", llvm::errs() << "\tmayClobber[6]\n");

  auto useAllocSites = getAllAllocSites(*usePtr, cache);
  if (!useAllocSites.hasValue())
    return true;

  LOG("shadow_optimizer", llvm::errs() << "\tmayClobber[7]\n");

  auto defAllocSites = getAllAllocSites(*defPtr, cache);
  if (!defAllocSites.hasValue())
    return true;

  LOG("shadow_optimizer", llvm::errs() << "\tmayClobber[8]\n");

  for (auto *as : *useAllocSites)
    if (defAllocSites->count(as) > 0)
      return true;

  LOG("shadow_optimizer", llvm::errs() << "\tmayClobber[9]\n");

  return false;
}

void ShadowDsaImpl::solveUses(Function &F) {
  unsigned numOptimized = 0;

  AllocSitesCache ptrToAllocSitesCache;

  // Visit shadow loads in topological order.
  for (auto *bb : llvm::inverse_post_order(&F.getEntryBlock()))
    for (auto &inst : *bb)
      if (auto *call = dyn_cast<CallInst>(&inst))
        if (call->getMetadata(m_memUseTag)) {
          LOG("shadow_optimizer", llvm::errs() << "Solving " << *call << "\n");

          // Find the first potentially clobbering memDef (shadow store or
          // shadow init).
          CallInst *oldDef = nullptr;
          CallInst *def = &getParentDef(*call);
          while (oldDef != def &&
                 !mayClobber(*def, *call, ptrToAllocSitesCache)) {
            oldDef = def;
            def = &getParentDef(*def);
          }

          LOG("shadow_optimizer", llvm::errs() << "Def for: " << *call
                                               << "\n\tis " << *def << "\n");

          if (call->getOperand(1) != def) {
            ++numOptimized;
            call->setArgOperand(1, def);
          }
        }

  LOG("shadow_optimizer", llvm::errs() << "MemSSA optimizer: " << numOptimized
                                       << " use(s) solved.\n");
}

} // namespace

namespace seahorn {

bool ShadowMemSeaDsa::runOnModule(llvm::Module &M) {
  if (M.begin() == M.end())
    return false;

  dsa::GlobalAnalysis &dsa = getAnalysis<dsa::DsaAnalysis>().getDsaAnalysis();
  TargetLibraryInfo &tli = getAnalysis<TargetLibraryInfoWrapperPass>().getTLI();

  CallGraph *cg = nullptr;
  auto cgPass = getAnalysisIfAvailable<CallGraphWrapperPass>();
  if (cgPass)
    cg = &cgPass->getCallGraph();

  dsa::AllocSiteInfo &asi = getAnalysis<dsa::AllocSiteInfo>();

  LOG("shadow_verbose", errs() << "Module before shadow insertion:\n"
                               << M << "\n";);

  ShadowDsaImpl impl(dsa, asi, tli, cg, *this, SplitFields, LocalReadMod);
  bool res = impl.runOnModule(M);
  LOG("shadow_verbose", errs() << "Module after shadow insertion:\n"
                               << M << "\n";);

  // -- verifyModule returns true if module is broken
  assert(!llvm::verifyModule(M, &errs()));
  return res;
}

void ShadowMemSeaDsa::getAnalysisUsage(llvm::AnalysisUsage &AU) const {
  AU.addRequiredTransitive<dsa::DsaAnalysis>();
  AU.addRequired<dsa::AllocSiteInfo>();
  AU.addRequired<llvm::CallGraphWrapperPass>();
  AU.addRequired<llvm::DominatorTreeWrapperPass>();
  AU.addRequired<llvm::TargetLibraryInfoWrapperPass>();
  AU.addRequired<llvm::AssumptionCacheTracker>();
  AU.setPreservesAll();
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
        "shadow.mem.global.init", "shadow.mem.arg.mod"};
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
