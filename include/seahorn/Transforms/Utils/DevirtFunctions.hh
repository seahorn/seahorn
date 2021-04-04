#pragma once

/**  Program transformation to replace indirect calls with direct calls **/

#include "seahorn/config.h"
#include "llvm/ADT/DenseMap.h"
#include "llvm/ADT/SmallVector.h"
#include "llvm/IR/InstVisitor.h"

#include <memory>

namespace llvm {
class Module;
class Function;
class CallSite;
class PointerType;
class CallGraph;
} // namespace llvm

namespace seadsa {
class CompleteCallGraphAnalysis;
} // namespace seadsa

namespace seahorn {

namespace devirt_impl {
using AliasSetId = const llvm::PointerType *;

/// returns an id of an alias set to which this function belongs
/// requires that CS is an indirect call through a function pointer
AliasSetId typeAliasId(const llvm::Function &F);

/// returns an id of an alias set of the called value
AliasSetId typeAliasId(llvm::CallSite &CS);
} // end namespace devirt_impl

enum class CallSiteResolverKind {
  RESOLVER_TYPES,
  RESOLVER_CHA,
  RESOLVER_SEADSA
};

/*
 * Generic class API for resolving indirect calls
 */
class CallSiteResolver {
protected:
  CallSiteResolverKind m_kind;
  CallSiteResolver(CallSiteResolverKind kind) : m_kind(kind) {}

public:
  using AliasSetId = devirt_impl::AliasSetId;
  using AliasSet = llvm::SmallVector<const llvm::Function *, 16>;

  virtual ~CallSiteResolver() {}

  CallSiteResolverKind get_kind() const { return m_kind; }

  /* Return all the possible callees for CS.
     It can return nullptr if not callees found.
     If isComplete is true then all the possible callees are known.
  */
  virtual const AliasSet *getTargets(llvm::CallSite &CS, bool &isComplete) = 0;

#ifdef USE_BOUNCE_FUNCTIONS
  /* Return a bounce function that resolves CS. It can return null if
     no bounce function. */
  virtual llvm::Function *getBounceFunction(llvm::CallSite &CS) = 0;

  /* Cache a bounce function for the callee */
  virtual void cacheBounceFunction(llvm::CallSite &CS,
                                   llvm::Function *bounce) = 0;
#endif
};

// forward declaration
class ClassHierarchyAnalysis;

/*
 * Resolve an indirect call by selecting all functions defined in the
 * same module whose type signature matches with the callsite.
 */
class CallSiteResolverByTypes : public CallSiteResolver {
public:
  using AliasSetId = CallSiteResolver::AliasSetId;
  using AliasSet = CallSiteResolver::AliasSet;

  CallSiteResolverByTypes(llvm::Module &M);

  virtual ~CallSiteResolverByTypes();

  const AliasSet *getTargets(llvm::CallSite &CS, bool &isComplete) override;

#ifdef USE_BOUNCE_FUNCTIONS
  llvm::Function *getBounceFunction(llvm::CallSite &CS) override;

  void cacheBounceFunction(llvm::CallSite &CS, llvm::Function *bounce) override;
#endif

private:
  /* invariant: the value in TargetsMap's entries is sorted */
  using TargetsMap = llvm::DenseMap<AliasSetId, AliasSet>;
#ifdef USE_BOUNCE_FUNCTIONS
  using BounceMap = llvm::DenseMap<AliasSetId, llvm::Function *>;
#endif

  // -- the module
  llvm::Module &m_M;
  // -- map from alias-id to the corresponding targets
  TargetsMap m_targets_map;
#ifdef USE_BOUNCE_FUNCTIONS
  // -- map alias set id to an existing bounce function
  BounceMap m_bounce_map;
#endif
  void populateTypeAliasSets(void);
};

/*
 * Resolve indirect call by using sea-dsa pointer analysis refined
 * with types.
 */
class CallSiteResolverByDsa final : public CallSiteResolver {
public:
  using AliasSetId = CallSiteResolverByTypes::AliasSetId;
  using AliasSet = CallSiteResolverByTypes::AliasSet;

  CallSiteResolverByDsa(llvm::Module &M,
                        seadsa::CompleteCallGraphAnalysis &dsa);

  ~CallSiteResolverByDsa() = default;

  const AliasSet *getTargets(llvm::CallSite &CS, bool &isComplete) override;

#ifdef USE_BOUNCE_FUNCTIONS
  llvm::Function *getBounceFunction(llvm::CallSite &CS) override;

  void cacheBounceFunction(llvm::CallSite &CS,
                           llvm::Function *bounceFunction) override;
#endif

private:
  /* invariant: the value in TargetsMap's entries is sorted */
  using TargetsMap = llvm::DenseMap<llvm::Instruction *, AliasSet>;
#ifdef USE_BOUNCE_FUNCTIONS
  using BounceMap =
      std::multimap<AliasSetId, std::pair<const AliasSet *, llvm::Function *>>;
#endif

  // -- the module
  llvm::Module &m_M;
  // -- the pointer analysis to resolve function pointers
  seadsa::CompleteCallGraphAnalysis &m_dsa;
  // -- map from callsite to the corresponding alias set
  TargetsMap m_targets_map;
#ifdef USE_BOUNCE_FUNCTIONS
  // -- map from alias set id + dsa targets to an existing bounce function
  BounceMap m_bounce_map;
#endif
};

/*
 *  Resolve C++ virtual calls using Class Hierarchy Analysis.
 */
class CallSiteResolverByCHA final : public CallSiteResolver {
public:
  using AliasSetId = CallSiteResolver::AliasSetId;
  using AliasSet = CallSiteResolver::AliasSet;

  CallSiteResolverByCHA(llvm::Module &M);

  ~CallSiteResolverByCHA();

  const AliasSet *getTargets(llvm::CallSite &CS, bool &isComplete) override;

#ifdef USE_BOUNCE_FUNCTIONS
  llvm::Function *getBounceFunction(llvm::CallSite &CS) override;

  void cacheBounceFunction(llvm::CallSite &CS, llvm::Function *bounce) override;
#endif

private:
  std::unique_ptr<ClassHierarchyAnalysis> m_cha;
};

//
// Class: DevirtualizeFunctions
//
//  This transform pass will look for indirect function calls and
//  transform them into a switch statement that selects one of
//  several direct function calls to execute. This transformation
//  pass is parametric on the method used to resolve the call.
//
class DevirtualizeFunctions : public llvm::InstVisitor<DevirtualizeFunctions> {

private:
  using AliasSet = CallSiteResolver::AliasSet;
  using AliasSetId = devirt_impl::AliasSetId;

  // Call graph of the program
  llvm::CallGraph *m_cg;

#ifdef USE_BOUNCE_FUNCTIONS
  /// maps alias set id to an existing bounce function
  llvm::DenseMap<AliasSetId, llvm::Function *> m_bounceMap;
#endif

  // Worklist of call sites to transform
  llvm::SmallVector<llvm::Instruction *, 32> m_worklist;

  // allow creating of indirect calls during devirtualization
  // (required for soundness)
  bool m_allowIndirectCalls;

  /// turn the indirect call-site into a direct one
  void mkDirectCall(llvm::CallSite CS, CallSiteResolver *CSR);

#ifdef USE_BOUNCE_FUNCTIONS
  /// create a bounce function that calls functions directly
  llvm::Function *mkBounceFn(llvm::CallSite &CS, CallSiteResolver *CSR);
#endif

public:
  DevirtualizeFunctions(llvm::CallGraph *cg, bool allowIndirectCalls);

  ~DevirtualizeFunctions();

  // Resolve all indirect calls in the Module using a particular
  // callsite resolver.
  bool resolveCallSites(llvm::Module &M, CallSiteResolver *CSR);

  // -- VISITOR IMPLEMENTATION --

  void visitCallSite(llvm::CallSite CS);
  void visitCallInst(llvm::CallInst &CI);
  void visitInvokeInst(llvm::InvokeInst &II);
};

} // namespace seahorn
