#pragma once

#include "llvm/ADT/SmallVector.h"
#include <memory>

/** Perform Class Hierarch Analysis for C++ programs **/

namespace llvm {
class Module;
class Function;
class ImmutableCallSite;
class raw_ostream;
} // namespace llvm

namespace seahorn {

class ClassHierarchyAnalysis_Impl;

class ClassHierarchyAnalysis {
public:
  using function_vector_t = llvm::SmallVector<const llvm::Function *, 16>;

  ClassHierarchyAnalysis(llvm::Module &M);

  ~ClassHierarchyAnalysis();

  /*
   * Build the class hierarchy graph and reconstruct vtables
   */
  void calculate(void);

  /* Return true if the callsite is a virtual call which has been
     resolved */
  bool isVCallResolved(const llvm::ImmutableCallSite &CS) const;

  /* Return all possible callees for the C++ virtual call.
   *  If CS is not a virtual call then it returns an empty set.
   */
  const function_vector_t& getVCallCallees(const llvm::ImmutableCallSite &CS);
  
  /*
   * Print the class hierarchy graph
   */
  void printClassHierarchy(llvm::raw_ostream &o) const;

  /*
   * Print for each class its vtable
   */
  void printVtables(llvm::raw_ostream &o) const;

  /*
   * Print some stats about the analysis
   */
  void printStats(llvm::raw_ostream &o) const;

private:
  std::unique_ptr<ClassHierarchyAnalysis_Impl> m_cha_impl;  
};

} // namespace seahorn
