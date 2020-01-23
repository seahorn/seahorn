#pragma once

/**  Program transformation to replace indirect calls with direct calls **/

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

namespace seahorn {

namespace devirt_impl {
using AliasSetId = const llvm::PointerType *;

/// returns an id of an alias set to which this function belongs
/// requires that CS is an indirect call through a function pointer
AliasSetId typeAliasId(const llvm::Function &F);

/// returns an id of an alias set of the called value
AliasSetId typeAliasId(llvm::CallSite &CS);
} // end namespace devirt_impl

enum class CallSiteResolverKind { RESOLVER_TYPES, RESOLVER_CHA };

/*
 * Generic class API for resolving indirect calls
 */
class CallSiteResolver {
  CallSiteResolverKind m_kind;

protected:
  CallSiteResolver(CallSiteResolverKind kind) : m_kind(kind) {}

public:
  using AliasSetId = devirt_impl::AliasSetId;    
  using AliasSet = llvm::SmallVector<const llvm::Function *, 16>;

  virtual ~CallSiteResolver() {}

  CallSiteResolverKind get_kind() const { return m_kind; }

  /* out contains all the callees to resolve CS */
  virtual void getTargets(llvm::CallSite &CS, AliasSet &out) = 0;

  /* for reusing bounce functions */
  virtual llvm::Function* getBounceFunction(llvm::CallSite &CS) = 0;
  virtual void cacheBounceFunction(llvm::CallSite &CS, llvm::Function* bounce) = 0;
};

// forward declaration
class ClassHierarchyAnalysis;

/*
 * Resolve an indirect call by selecting all functions defined in the
 * same module whose type signature matches with the callsite.
 */
class CallSiteResolverByTypes final : public CallSiteResolver {
public:
  using AliasSetId = CallSiteResolver::AliasSetId;  
  using AliasSet = CallSiteResolver::AliasSet;
  
  CallSiteResolverByTypes(llvm::Module &M);

  virtual ~CallSiteResolverByTypes();

  void getTargets(llvm::CallSite &CS, AliasSet &out);

  llvm::Function* getBounceFunction(llvm::CallSite& CS);
  
  void cacheBounceFunction(llvm::CallSite& CS, llvm::Function* bounce);
  
private:

  using TargetsMap = llvm::DenseMap<AliasSetId, AliasSet>;
  using BounceMap = llvm::DenseMap<AliasSetId, llvm::Function *>;
  
  // -- the module
  llvm::Module &m_M;
  // -- map from alias-id to the corresponding targets
  TargetsMap m_targets_map;
  // -- map alias set id to an existing bounce function
  BounceMap m_bounce_map;
  
  void populateTypeAliasSets(void);
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

  void getTargets(llvm::CallSite &CS, AliasSet &out);

  llvm::Function* getBounceFunction(llvm::CallSite& CS);
  
  void cacheBounceFunction(llvm::CallSite& CS, llvm::Function* bounce);
  
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

  /// maps alias set id to an existing bounce function
  llvm::DenseMap<AliasSetId, llvm::Function *> m_bounceMap;

  // Worklist of call sites to transform
  llvm::SmallVector<llvm::Instruction *, 32> m_worklist;

  // allow creating of indirect calls during devirtualization
  // (required for soundness)
  bool m_allowIndirectCalls;
  
  /// turn the indirect call-site into a direct one
  void mkDirectCall(llvm::CallSite CS, CallSiteResolver *CSR);

  /// create a bounce function that calls functions directly
  llvm::Function *mkBounceFn(llvm::CallSite &CS, CallSiteResolver *CSR);

public:
  DevirtualizeFunctions(llvm::CallGraph *cg, bool allowIndirectCalls);

  ~DevirtualizeFunctions();
  
  // Resolve all indirect calls in the Module using a particular
  // callsite resolver.
  bool resolveCallSites(llvm::Module &M, CallSiteResolver *CSR);

  // -- VISITOR IMPLEMENTATION --

  void visitCallSite(llvm::CallSite &CS);
  void visitCallInst(llvm::CallInst &CI);
  void visitInvokeInst(llvm::InvokeInst &II);
};

} // namespace seahorn
