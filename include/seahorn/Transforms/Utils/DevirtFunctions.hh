#pragma once

/**  Program transformation to replace indirect calls with direct calls **/

#include "llvm/ADT/DenseMap.h"
#include "llvm/ADT/SmallVector.h"
#include "llvm/IR/InstVisitor.h"

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

/*
   Generic class API for resolving indirect calls
*/
class CallSiteResolver {
public:
  using AliasSet = llvm::SmallVector<const llvm::Function *, 16>;

  virtual ~CallSiteResolver() {}
  /* out contains all the callees to resolve CS */
  virtual void getTargets(llvm::CallSite &CS, AliasSet &out) = 0;
};

/*
    Resolve an indirect call by selecting all functions defined in the
    same module whose type signature matches with the callsite.
 */
class CallSiteResolverByTypes : public CallSiteResolver {
  using AliasSetId = devirt_impl::AliasSetId;
  using TypeAliasSetMap = llvm::DenseMap<AliasSetId, AliasSet>;

  // -- the module
  llvm::Module &m_M;
  // -- map from alias-id to the corresponding alias set
  TypeAliasSetMap m_typeAliasSets;

  void populateTypeAliasSets(void);

public:
  CallSiteResolverByTypes(llvm::Module &M);
  void getTargets(llvm::CallSite &CS, AliasSet &out);
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

  /// turn the indirect call-site into a direct one
  void mkDirectCall(llvm::CallSite CS, CallSiteResolver *CSR,
                    bool AllowIndirectCalls);

  /// create a bounce function that calls functions directly
  llvm::Function *mkBounceFn(llvm::CallSite &CS, CallSiteResolver *CSR,
                             bool AllowIndirectCalls);

public:
  DevirtualizeFunctions(llvm::CallGraph *cg);

  // Resolve all indirect calls in the Module using a particular
  // callsite resolver.
  bool resolveCallSites(llvm::Module &M, CallSiteResolver *CSR,
                        /* allow creating of indirect calls during
                           devirtualization (required for
                           soundness) */
                        bool AllowIndirectCalls = false);

  // -- VISITOR IMPLEMENTATION --

  void visitCallSite(llvm::CallSite &CS);
  void visitCallInst(llvm::CallInst &CI);
  void visitInvokeInst(llvm::InvokeInst &II);
};

} // namespace seahorn
