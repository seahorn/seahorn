#pragma once

#include <vector>

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
  ClassHierarchyAnalysis(llvm::Module &M);

  ~ClassHierarchyAnalysis();

  /*
   * Build the class hierarchy graph and reconstruct vtables
  */
  void calculate(void);

  /*
   * Return true if the callsite migth have been originated from a C++
   * virtual call. out contains all the possible callees.
  */
  bool resolveVirtualCall(const llvm::ImmutableCallSite &CS,
                          std::vector<llvm::Function *> &out) const;

  /* 
   * Print the class hierarchy graph 
   */
  void printClassHierarchy(llvm::raw_ostream &o) const;

  /* 
   * Print for each class its vtable 
   */
  void printVtables(llvm::raw_ostream &o) const;

private:
  ClassHierarchyAnalysis_Impl *m_cha_impl;
};

} // namespace seahorn
