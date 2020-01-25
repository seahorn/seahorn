#include "seahorn/Analysis/ClassHierarchyAnalysis.hh"

#include "seahorn/Support/SeaDebug.h"
#include "seahorn/Support/SeaLog.hh"
#include "llvm/ADT/DenseMap.h"
#include "llvm/ADT/SmallSet.h"
#include "llvm/ADT/SmallVector.h"
#include "llvm/IR/CallSite.h"
#include "llvm/IR/Constants.h"
#include "llvm/IR/InstIterator.h"
#include "llvm/IR/Module.h"
#include "llvm/IR/Value.h"

#include <boost/algorithm/string/find.hpp>
#include <boost/algorithm/string/predicate.hpp>
#include <cxxabi.h>

/*
   #Background about virtual calls in LLVM#

   To implement virtual functions, C++ uses a special form of late
   binding known as the virtual table (aka vtable). The vtable is a
   lookup table of functions used to resolve function calls
   dynamically.

   First, every class that calls virtual functions (or is derived from
   a class that calls virtual functions) is given its own vtable. This
   vtable is a static array that the compiler sets up at compile
   time. A vtable contains one entry for each virtual function that
   can be called by objects of the class. Each entry in this vtable is
   a function pointer that points to the **most-derived** function
   accessible by that class (e.g., if a method is not implemented by a
   subclass C then C's vtable will have a function pointer to some
   ancestor's vtable).  Actually a vtable contains more than function
   pointers. For instance, it contains also the type name identified
   to the class (called typeinfo).

   Second, the compiler adds a hidden pointer to the base class, which
   we will call _vptr_. Very importantly, vptr is inherited by derived
   classes. vptr is set (automatically) when a class object is created
   so that it points to the virtual table for that class.

   Resources:
    - https://itanium-cxx-abi.github.io/cxx-abi/abi.html
    - https://ww2.ii.uj.edu.pl/~kapela/pn/cpp_vtable.html

   Examples of vtables
   -------------------

   1. For simple inheritance the vtable might look like this:

     class B {
        virtual int f1() = 0;
        virtual int f2(int) = 0;
        virtual int f3() { return 0;}
     };
     class D1: public B { ... }

     ;; vtable for D1
     @_ZTV2D1 = linkonce_odr unnamed_addr constant { [6 x i8*] }
     { [6 x i8*] [
                 ;; zero top-offset
                 i8* null,
                 ;;typeinfo for D1
                 i8* bitcast ({ i8*, i8*, i8* }* @_ZTI2D1 to i8*),
                 ;; D1::~D1()
                 i8* bitcast (void (%class.D1*)* @_ZN2D1D1Ev to i8*),
                 ;; D1::f1()
                 i8* bitcast (i32 (%class.D1*)* @_ZN2D12f1Ev to i8*),
                 ;; D1::f2(int)
                 i8* bitcast (i32 (%class.D1*, i32)* @_ZN2D12f2Ei to i8*),
                 ;; B::f3()
                 i8* bitcast (i32 (%class.B*)* @_ZN1B2f3Ev to i8*)] }

   2. For multiple inheritance the vtable might look like this:

      class A {
         virtual int f() { return 0; }
      };
      class B {
         virtual int f() { return 0; }
      };
      class C: public A, B { ... }

      ;;; vtable for C
      @_ZTV1C = internal unnamed_addr constant { [6 x i8*], [5 x i8*] } {
         [6 x i8*] [i8* null,
                    ;;; typeinfo for C
                    i8* bitcast ({ i8*, i8*, i32, i32, i8*, i32, i8*, i32 }*
   @_ZTI1C to i8*), i8* bitcast (void (%class.C*)* @_ZN1CD1Ev to i8*), i8*
   bitcast (void (%class.C*)* @_ZN1CD0Ev to i8*), i8* bitcast (i32 (%class.C*)*
   @_ZN1C1fEv to i8*), i8* bitcast (i32 (%class.C*)* @_ZN1C1gEv to i8*)],
         ;;; non-virtual thunk methods (for B)
         [5 x i8*] [i8* inttoptr (i32 -4 to i8*),
                    ;;; typeinfo for C
                    i8* bitcast ({ i8*, i8*, i32, i32, i8*, i32, i8*, i32 }*
   @_ZTI1C to i8*), i8* bitcast (void (%class.C*)* @_ZThn4_N1CD1Ev to i8*), i8*
   bitcast (void (%class.C*)* @_ZThn4_N1CD0Ev to i8*), i8* bitcast (i32
   (%class.C*)* @_ZThn4_N1C1gEv to i8*)] }

   In cases of multiple inheritance, the compiler usually puts
   together multiple vtables in one.  Thunk functions are introduced
   by the compiler to do some pointer correction when multiple vtables
   are stored together.


   3. For diamond *virtual* inheritance  the vtable my look like this:
      class A {
         virtual int f() { return 0;}
      };
      class B: virtual public A { ... }
      class C: virtual public A { ... }
      class D: public B, C { ... }

      ;; vtable for D
      @_ZTV1D = internal unnamed_addr constant { [8 x i8*], [8 x i8*] }
             { [8 x i8*] [i8* null,
                          i8* null,
                          i8* null,
                          i8* null,
                          ;;; typeinfo for D
                          i8* bitcast ({ i8*, i8*, i32, i32, i8*, i32, i8*, i32
   }* @_ZTI1D to i8*), i8* bitcast (void (%class.D*)* @_ZN1DD1Ev to i8*), i8*
   bitcast (void (%class.D*)* @_ZN1DD0Ev to i8*), i8* bitcast (i32 (%class.D*)*
   @_ZN1D1fEv to i8*)], [8 x i8*] [i8* inttoptr (i32 -4 to i8*), i8* inttoptr
   (i32 -4 to i8*), i8* inttoptr (i32 -4 to i8*), i8* inttoptr (i32 -4 to i8*),
                          ;; typeinfo for D
                          i8* bitcast ({ i8*, i8*, i32, i32, i8*, i32, i8*, i32
   }* @_ZTI1D to i8*), i8* bitcast (void (%class.D*)* @_ZThn4_N1DD1Ev to i8*),
                          i8* bitcast (void (%class.D*)* @_ZThn4_N1DD0Ev to
   i8*), i8* bitcast (i32 (%class.D*)* @_ZThn4_N1D1fEv to i8*)] }, align 8

   #How we resolve virtual calls#

   Assumption: a C++ class is identified in LLVM bitcode as a named
   struct type.

   Initialization:

   1. Build a class hierarchy graph G. Each class in the module is a
      node (see above how we identify a class). We have an edge from
      c1 to c2 if c2 inherits from c1. Currently, the inheritance
      relationship is very weak because it's only based on the LLVM
      subtype relationship. Inheritance implies subtyping but not the
      opposite.

   2. We build a map from a class to its vtable.

      A vtable is identified when the demangled name of a global
      variable starts with "vtable for". A vtable in LLVM is a global
      constant array. We scan each array element and check if it
      contains a function. If yes, that is considered an entry in the
      vtable.

      We also identify the class associated to a vtable. While we scan
      each constant array element, we also check if the demangled name
      of an array element starts with "typeinfo for XXX". If yes, this
      is the typeinfo from the class. From there, we can extract the
      class name string XXX from which we can ask the Module to return
      the type associated to that name. This approach only works if
      the type is a named struct type. It's possible that the class
      associated to the typeinfo is external. In that case, we won't
      able to get from the Module a named struct type.

      Phasar and SVF get the class by inspecting the constructor. They
      identify a constructor as the function where the vptr is
      initialized. The class is obtained from the formal parameter of
      the constructor. We do not do that because when code is
      optimized constructors are inlined.


   For each indirect call we return the set of all possible callees as
   follows:

      First, we try to find the vtable index (i.e., which function is
      being called) using some code pattern. If successful then we
      extract the type of the first actual parameter and check if the
      type is a pointer to a named struct type. If successful, let us
      call this named struct type, the class C. Then, this is what we
      do roughly in pseudocode:

      callees := empty;
      reachable := all reachable classes from C using G;
      foreach c in reachable do:
          f := get(vtable(c), index);
          callees := callees U f;
      return callees;
 */
namespace seahorn {

using namespace llvm;

static std::string cxx_demangle(const std::string &mangled_name) {

  int status = 0;
  char *demangled =
      abi::__cxa_demangle(mangled_name.c_str(), NULL, NULL, &status);
  std::string result((status == 0 && demangled != NULL) ? demangled
                                                        : mangled_name);
  free(demangled);
  return result;
}

static Type *getNonPointerType(Type *pointer) {
  auto next = dyn_cast<PointerType>(pointer);
  while (next) {
    pointer = next->getElementType();
    next = dyn_cast<PointerType>(pointer);
  }
  return pointer;
}

class ClassHierarchyAnalysis_Impl {
public:
  using function_vector_t = ClassHierarchyAnalysis::function_vector_t;

  ClassHierarchyAnalysis_Impl(Module &Module)
      : m_module(Module), m_num_graph_nodes(0), m_num_graph_edges(0),
        m_num_graph_closed_edges(0), m_num_potential_vtables(0),
        m_num_vtables(0), m_num_potential_virtual_calls(0),
        m_num_resolved_virtual_calls(0) {}

  ~ClassHierarchyAnalysis_Impl() = default;

  void calculate(void);

  bool isVCallResolved(const llvm::ImmutableCallSite &CS) const;

  const function_vector_t& getVCallCallees(const llvm::ImmutableCallSite &CS);
  
  void printVtables(raw_ostream &o) const;

  void printClassHierarchy(raw_ostream &o) const;

  void printStats(raw_ostream &o) const;

private:
  using graph_t =
      DenseMap<const StructType *, SmallSet<const StructType *, 16>>;
  using vtable_t = SmallVector<Function *, 16>;
  using vtable_map_t = DenseMap<const StructType *, vtable_t>;
  using resolution_table_t = DenseMap<const Instruction*, function_vector_t>;
  
  Module &m_module;
  // -- class hierarchy graph (CHG)
  graph_t m_graph;
  // -- vtables
  vtable_map_t m_vtables;
  // -- remember resolved callsites that look like virtual calls
  DenseSet<const Instruction*> m_resolved_virtual_calls;
  // -- map a callsite to the set of all possible callees if the
  // -- callsite is a virtual call.
  resolution_table_t m_resolution_table;

  // some counters for stats
  unsigned m_num_graph_nodes;
  unsigned m_num_graph_edges;
  unsigned m_num_graph_closed_edges;
  unsigned m_num_potential_vtables;
  unsigned m_num_vtables;
  unsigned m_num_potential_virtual_calls;
  unsigned m_num_resolved_virtual_calls;

  void buildCHG(void);

  void buildVtables(void);

  void closureCHG();

  bool hasVtable(const StructType *ty) const;

  vtable_t &getVtable(const StructType *ty);

  const vtable_t &getVtable(const StructType *ty) const;

  void addCHGEdge(const StructType *src, const StructType *dest,
                  graph_t &graph);

  bool hasCHGEdge(const StructType *src, const StructType *dest,
                  graph_t &graph) const;

  void addCandidateFunction(const StructType *type, unsigned vtable_index,
                            const FunctionType *callsite_type,
                            SmallSet<Function *, 16> &out) const;

  // it's not const because it updates some counters for stats
  bool resolveVirtualCall(const llvm::ImmutableCallSite &CS,
                          function_vector_t &out);
  
  static int getVtableIndex(const ImmutableCallSite &CS);

  static bool matchVirtualSignature(const llvm::FunctionType *type_call,
                                    const llvm::FunctionType *type_candidate);
};

bool ClassHierarchyAnalysis_Impl::hasVtable(const StructType *ty) const {
  return m_vtables.find(ty) != m_vtables.end();
}

ClassHierarchyAnalysis_Impl::vtable_t &
ClassHierarchyAnalysis_Impl::getVtable(const StructType *ty) {
  assert(hasVtable(ty));
  auto it = m_vtables.find(ty);
  return it->second;
}

const ClassHierarchyAnalysis_Impl::vtable_t &
ClassHierarchyAnalysis_Impl::getVtable(const StructType *ty) const {
  assert(hasVtable(ty));
  auto it = m_vtables.find(ty);
  return it->second;
}

void ClassHierarchyAnalysis_Impl::addCHGEdge(const StructType *src,
                                             const StructType *dest,
                                             graph_t &g) {
  auto it = g.find(src);
  if (it != g.end()) {
    it->second.insert(dest);
  } else {
    SmallSet<const StructType *, 16> succs;
    succs.insert(dest);
    g.insert({src, succs});
  }
}

bool ClassHierarchyAnalysis_Impl::hasCHGEdge(const StructType *src,
                                             const StructType *dest,
                                             graph_t &g) const {
  auto it = g.find(src);
  if (it == g.end()) {
    return false;
  } else {
    return (it->second.count(dest));
  }
}

int ClassHierarchyAnalysis_Impl::getVtableIndex(const ImmutableCallSite &CS) {
  /*
    Assume the virtual call looks exactly like this:

     %33 = getelementptr inbounds i32 (%class.B*)*, i32 (%class.B*)** %32, i64 2
     %34 = load i32 (%class.B*)*, i32 (%class.B*)** %33, align 8
     %35 = call i32 %34(%class.B* %30)

   */
  if (const LoadInst *LI =
          dyn_cast<LoadInst>(CS.getCalledValue()->stripPointerCasts())) {
    if (const GetElementPtrInst *GEP =
            dyn_cast<GetElementPtrInst>(LI->getPointerOperand())) {
      if (ConstantInt *CI = dyn_cast<ConstantInt>(GEP->getOperand(1))) {
        return CI->getZExtValue();
      }
    }
  }
  return -1;
}

// Simple floyd-warshall implementation.
void ClassHierarchyAnalysis_Impl::closureCHG(void) {
  size_t num_nodes = m_graph.size();

  // the boolean adjacency matrix
  std::vector<std::vector<bool>> m(num_nodes);

  // 1. forall i,j:: m[i][j] = true iff exists an edge from node_i to node_j
  unsigned i = 0;
  for (auto &kv_i : m_graph) {
    m[i].reserve(num_nodes);
    for (auto &kv_j : m_graph) {
      if (hasCHGEdge(kv_i.first, kv_j.first, m_graph)) {
        m[i].push_back(true);
      } else {
        m[i].push_back(false);
      }
    }
    ++i;
  }

  LOG("cha-closure", errs() << "Boolean adjacency matrix before closure\n";
      for (unsigned i = 0; i < num_nodes; ++i) {
        for (unsigned j = 0; j < num_nodes; ++j) {
          errs() << "(" << i << "," << j << ")=" << m[i][j] << " ";
        }
        errs() << "\n";
      });

  // 2. forall i,j,k:: m[i][j] = m[i][j] | (m[i][k] & m[k][j])
  for (unsigned k = 0; k < num_nodes; ++k) {
    for (unsigned i = 0; i < num_nodes; ++i) {
      for (unsigned j = 0; j < num_nodes; ++j) {
        m[i][j] = m[i][j] | (m[i][k] & m[k][j]);
      }
    }
  }

  LOG("cha-closure", errs() << "Boolean adjacency matrix after closure\n";
      for (unsigned i = 0; i < num_nodes; ++i) {
        for (unsigned j = 0; j < num_nodes; ++j) {
          errs() << "(" << i << "," << j << ")=" << m[i][j] << " ";
        }
        errs() << "\n";
      });

  // Closed m_graph
  graph_t closed_g;
  auto it = m_graph.begin();
  for (unsigned i = 0; i < num_nodes; ++i, ++it) {
    auto jt = m_graph.begin();
    for (unsigned j = 0; j < num_nodes; ++j, ++jt) {
      if (m[i][j]) {
        addCHGEdge((*it).first, (*jt).first, closed_g);
        m_num_graph_closed_edges++;
      }
    }
  }
  std::swap(m_graph, closed_g);
}

void ClassHierarchyAnalysis_Impl::buildCHG(void) {
  // The construction of the class hierarchy graph is currently
  // imprecise.  For instance, in cases like this
  //    class A {
  //      B b;
  //    };
  //
  // we will add an edge from A to B even if there is no an
  // inheritance relationship between A and B.
  //
  // Phasar will prune this kind of spurious relationships by looking
  // at the constructor of B and removing any edge from X to B if
  // there is no a call to X's constructor in B's constructor.
  //
  // SVF also relies on the existence of constructors to add edges in
  // the class hierarchy graph.
  //
  // XXX: for now we don't rely on the existence of a constructor in
  // case program has been inlined.
  auto struct_types = m_module.getIdentifiedStructTypes();
  for (auto st : struct_types) {
    m_graph.insert({st, SmallSet<const StructType *, 16>()});
    m_num_graph_nodes++;
  }
  for (auto st : struct_types) {
    for (auto sub_ty : st->subtypes()) {
      if (const StructType *sub_st_ty = dyn_cast<const StructType>(sub_ty)) {
        addCHGEdge(sub_st_ty, st, m_graph);
        m_num_graph_edges++;
      }
    }
  }
}

void ClassHierarchyAnalysis_Impl::buildVtables(void) {

  const static std::string vtable_for_str = "vtable for";
  const static std::string typeinfo_for_str = "typeinfo for";
  const static std::string pure_virtual_str = "__cxa_pure_virtual";

  for (auto &gv : m_module.globals()) {

    // Vtables are constant global variables
    if (!isa<Constant>(gv)) {
      continue;
    }

    std::string demangled_gv_name = cxx_demangle(gv.getName().str());
    if (demangled_gv_name == "") {
      // the name could not be demangled
      continue;
    }

    // The demangled name of vtables start with "vtable for"
    if (demangled_gv_name.find(vtable_for_str) == std::string::npos) {
      continue;
    }

    // a vtable is a constant array where each array element is a
    if (!gv.hasInitializer()) {
      continue;
    }

    // We inspect the global initializer and try to figure if it
    // contains a vtable.  If yes, we extract typeinfo and functions
    // from the vtable.
    Constant *gv_initializer = gv.getInitializer();
    for (unsigned i = 0, e = gv_initializer->getNumOperands(); i < e; ++i) {
      if (ConstantArray *CA =
              dyn_cast<ConstantArray>(gv_initializer->getAggregateElement(i))) {
        // A vtable is a ConstantArray in LLVM so we are getting closer ...
        m_num_potential_vtables++;

        // We assume that a class can only have one typeinfo associated.
        StructType *class_typeinfo = nullptr;
        // the vtable
        vtable_t vtable;
        for (unsigned j = 0; j < CA->getNumOperands(); ++j) {
          if (ConstantExpr *CE =
                  dyn_cast<ConstantExpr>(CA->getAggregateElement(j))) {
            if (CE->isCast()) {
              if (Constant *Cast =
                      ConstantExpr::getBitCast(CE, CE->getType())) {
                /*
                 * Get typeinfo of the class
                 *
                 * XXX: typeinfo can be a named struct type if it's
                 *      internal to the module or i8* if it is
                 *      external. This code below will succeed only if
                 *      typeinfo is a named struct type.
                 */
                if (Cast->getOperand(0)->hasName()) {
                  std::string demangled_name(
                      cxx_demangle(Cast->getOperand(0)->getName().str()));
                  size_t pos = demangled_name.find_last_of(typeinfo_for_str);
                  if (pos != std::string::npos) {
                    /* here we know that the cast contains the typeinfo_ptr */
                    StructType *old_class_typeinfo = class_typeinfo;
                    // XXX: sometimes the compiler add the prefix
                    // "class." to the class name but not always.
                    std::string class_name = demangled_name.substr(pos + 1);
                    class_typeinfo =
                        m_module.getTypeByName("class." + class_name);
                    if (!class_typeinfo) {
                      class_typeinfo = m_module.getTypeByName(class_name);
                    }

                    if (old_class_typeinfo && class_typeinfo &&
                        old_class_typeinfo != class_typeinfo) {
                      ERR << "Found a vtable with two different typeinfo: "
                          << *old_class_typeinfo << " and " << *class_typeinfo;
                      llvm_unreachable(nullptr);
                    } else {
                      if (old_class_typeinfo && !class_typeinfo) {
                        // restore class_typeinfo
                        class_typeinfo = old_class_typeinfo;
                      }
                    }
                  }
                }
                // get the function and its offset
                if (Function *VF = dyn_cast<Function>(Cast->getOperand(0))) {
                  if (VF->getName() == pure_virtual_str) {
                    vtable.push_back(nullptr);
                  } else {
                    vtable.push_back(VF);
                  }
                }
              }
            }
          }
        }

        if (class_typeinfo) {
          m_vtables.insert({class_typeinfo, vtable});
          m_num_vtables++;
        } else {
          WARN << "We found something that looks a vtable but we couldn't find "
                  "typeinfo: "
               << *CA;
        }
      }
    }
  } // end outer loop
}

void ClassHierarchyAnalysis_Impl::calculate(void) {
  buildCHG();
  buildVtables();
  closureCHG();

  for (auto &F: m_module) {
    for (auto &I: llvm::make_range(inst_begin(&F), inst_end(&F))) {
      if (!isa<CallInst>(&I) && !isa<InvokeInst>(&I))
	continue;
      ImmutableCallSite CS(&I);
      function_vector_t callees;
      if (resolveVirtualCall(CS, callees)) {
	m_resolved_virtual_calls.insert(CS.getInstruction());
	m_resolution_table.insert(std::make_pair(CS.getInstruction(), callees));
      }
    }
  }
}

// In general, type_call and type_candidate are different because of the first
// argument.
bool ClassHierarchyAnalysis_Impl::matchVirtualSignature(
    const llvm::FunctionType *type_call,
    const llvm::FunctionType *type_candidate) {
  if (type_call->getNumParams() >= 1 &&
      type_call->getNumParams() == type_candidate->getNumParams() &&
      type_call->getReturnType() == type_candidate->getReturnType()) {
    // We skip the first argument
    for (unsigned int i = 1, e = type_call->getNumParams(); i < e; ++i) {
      if (type_call->getParamType(i) != type_candidate->getParamType(i)) {
        return false;
      }
    }
    return true;
  }
  return false;
}

void ClassHierarchyAnalysis_Impl::addCandidateFunction(
    const StructType *type, unsigned vtable_index,
    const FunctionType *callsite_type, SmallSet<Function *, 16> &out) const {
  if (hasVtable(type)) {
    const vtable_t &callees = getVtable(type);
    // XXX: a vtable can have null entries which mean virtual
    // functions.
    if (vtable_index < callees.size()) {
      if (Function *callee = callees[vtable_index]) {
        // XXX: callee can be null if we access to some vtable offset
        // which is not a function.
        if (matchVirtualSignature(callsite_type, callee->getFunctionType())) {
          out.insert(callees[vtable_index]);
        } else {
          ERR << "Did not match " << *callsite_type << " and "
              << *(callee->getFunctionType());
        }
      }
    } else {
      ERR << "Out-of-bounds access to vtable " << type->getName();
      llvm_unreachable(nullptr);
    }
  }
}

// Return the type of the first actual parameter if the call looks
// virtual. (temporary for stats)
bool mayBeVirtualCall(const ImmutableCallSite &CS) {

  // if not indirect call then we bail out ...
  if (CS.getCalledFunction()) {
    return false;
  }

  // If the callee is not a pointer to a function then we bail out ...
  if (!CS.getCalledValue()->getType()->isPointerTy()) {
    return false;
  }

  const FunctionType *CS_type = dyn_cast<FunctionType>(
      CS.getCalledValue()->getType()->getPointerElementType());
  if (!CS_type) {
    return false;
  }
  // Assume the first argument of CS is this, otherwise we bail out ...
  const Value *this_ = CS.getArgOperand(0);
  if (this_->getType()->isPointerTy()) {
    if (const StructType *this_type =
            dyn_cast<StructType>(this_->getType()->getPointerElementType())) {
      return true;
    }
  }
  return false;
}

bool ClassHierarchyAnalysis_Impl::resolveVirtualCall(
    const ImmutableCallSite &CS, function_vector_t &out) {

  // if not indirect call then we bail out ...
  if (CS.getCalledFunction()) {
    return false;
  }

  // If the callee is not a pointer to a function then we bail out ...
  if (!CS.getCalledValue()->getType()->isPointerTy()) {
    return false;
  }

  const FunctionType *CS_type = dyn_cast<FunctionType>(
      CS.getCalledValue()->getType()->getPointerElementType());
  if (!CS_type) {
    return false;
  }
  // Assume the first argument of CS is this, otherwise we bail out ...
  const Value *this_ = CS.getArgOperand(0);
  if (this_->getType()->isPointerTy()) {
    if (const StructType *this_type =
            dyn_cast<StructType>(this_->getType()->getPointerElementType())) {

      m_num_potential_virtual_calls++;

      int vtable_index = getVtableIndex(CS);
      if (vtable_index < 0) {
        WARN << "Cannot find vtable index for indirect call:\n "
             << "\t" << *(CS.getInstruction());
        return false;
      }

      // use a set to avoid duplicates. The same function can be in
      // multiple vtables.
      SmallSet<Function *, 16> out_set;
      auto it = m_graph.find(this_type);
      if (it != m_graph.end()) {
        // Add all possible candidates from reachable types in the
        // class hierarchy graph.
        auto &reachable_types = it->second;
        for (const StructType *type : reachable_types) {
          addCandidateFunction(type, vtable_index, CS_type, out_set);
        }
      }

      // We need to add also this_type. If this_type defines the
      // method as pure virtual then the method won't be added since
      // we won't find an internal function in the LLVM module.
      addCandidateFunction(this_type, vtable_index, CS_type, out_set);

      std::copy(out_set.begin(), out_set.end(), std::back_inserter(out));

      // true means that the callsite looks like a virtual call
      if (!out.empty()) {
        m_num_resolved_virtual_calls++;
      }
      return true;
    }
  }

  WARN << "Cannot resolve virtual call " << *CS.getInstruction()
       << " because first argument is not StructType\n";

  return false;
}

void ClassHierarchyAnalysis_Impl::printVtables(raw_ostream &o) const {
  for (auto &kv : m_vtables) {
    const StructType *class_ty = kv.first;
    auto const &funs = kv.second;
    o << cxx_demangle(class_ty->getName().str()) << ":\n";
    for (unsigned i = 0, e = funs.size(); i < e; ++i) {
      if (funs[i]) {
        o << "\t" << i << ": " << funs[i]->getName().str() << "   "
          << "DEMANGLED NAME=" << cxx_demangle(funs[i]->getName().str())
          << "   TYPE=" << *(funs[i]->getType()) << "\n";
      }
    }
  }
}

void ClassHierarchyAnalysis_Impl::printClassHierarchy(raw_ostream &o) const {
  for (auto &kv : m_graph) {
    const StructType *node = kv.first;
    auto const &succs = kv.second;
    o << cxx_demangle(node->getName().str()) << " --> "
      << "{";
    for (auto it = succs.begin(), et = succs.end(); it != et;) {
      o << cxx_demangle(((*it)->getName().str()));
      it++;
      if (it != et) {
        o << ",";
      }
    }
    o << "}\n";
  }
}

bool ClassHierarchyAnalysis_Impl::
isVCallResolved(const llvm::ImmutableCallSite &CS) const {
  return m_resolved_virtual_calls.count(CS.getInstruction()) > 0;
}

const ClassHierarchyAnalysis_Impl::function_vector_t&
ClassHierarchyAnalysis_Impl::getVCallCallees(const llvm::ImmutableCallSite &CS) {
  return m_resolution_table[CS.getInstruction()];
}

void ClassHierarchyAnalysis_Impl::printStats(raw_ostream &o) const {
  errs() << "=== CHA stats===\n";
  errs() << "BRUNCH_STAT GRAPH NUMBER NODES " << m_num_graph_nodes << "\n";
  errs() << "BRUNCH_STAT GRAPH NUMBER EDGES " << m_num_graph_edges << "\n";
  errs() << "BRUNCH_STAT GRAPH NUMBER CLOSED EDGES " << m_num_graph_closed_edges
         << "\n";
  errs() << "BRUNCH_STAT POTENTIAL VTABLES " << m_num_potential_vtables << "\n";
  errs() << "BRUNCH_STAT IDENTIFIED VTABLES " << m_num_vtables << "\n";
  errs() << "BRUNCH_STAT POTENTIAL VIRTUAL CALLS "
         << m_num_potential_virtual_calls << "\n";
  errs() << "BRUNCH_STAT RESOLVED VIRTUAL CALLS "
         << m_num_resolved_virtual_calls << "\n";
}

/** ClassHierarchyAnalysis methods **/
ClassHierarchyAnalysis::ClassHierarchyAnalysis(Module &M)
  : m_cha_impl(make_unique<ClassHierarchyAnalysis_Impl>(M)) {}

ClassHierarchyAnalysis::~ClassHierarchyAnalysis(void) {
}

void ClassHierarchyAnalysis::calculate(void) {
  m_cha_impl->calculate();
}

bool ClassHierarchyAnalysis::
isVCallResolved(const llvm::ImmutableCallSite &CS) const {
  return m_cha_impl->isVCallResolved(CS);
}

const ClassHierarchyAnalysis::function_vector_t&
ClassHierarchyAnalysis::getVCallCallees(const llvm::ImmutableCallSite &CS) {
  return m_cha_impl->getVCallCallees(CS);
}

void ClassHierarchyAnalysis::printClassHierarchy(raw_ostream &o) const {
  m_cha_impl->printClassHierarchy(o);
}

void ClassHierarchyAnalysis::printVtables(raw_ostream &o) const {
  m_cha_impl->printVtables(o);
}

void ClassHierarchyAnalysis::printStats(raw_ostream &o) const {
  m_cha_impl->printStats(o);
}

/** LLVM pass **/
class ClassHierarchyAnalysisPass : public ModulePass {
public:
  static char ID;

  ClassHierarchyAnalysisPass()
    : ModulePass(ID), m_cha(nullptr) {}

  ~ClassHierarchyAnalysisPass() = default;

  bool runOnModule(Module &M) {
    m_cha.reset(new ClassHierarchyAnalysis(M));
    m_cha->calculate();

    errs() << "=== Class Hierarchy Graph ===\n";
    m_cha->printClassHierarchy(errs());
    errs() << "\n=== Vtables ===\n";
    m_cha->printVtables(errs());
    errs() << "\n=== Devirtualization===\n";
    for (auto &F : M) {
      for (auto &I: llvm::make_range(inst_begin(&F), inst_end(&F))) {
	if (!isa<CallInst>(&I) && !isa<InvokeInst>(&I))
	  continue;
	ImmutableCallSite CS(&I);
	if (!m_cha->isVCallResolved(CS)) {
	  continue;
	}
	auto const& callees = m_cha->getVCallCallees(CS);
	errs() << "** Found virtual call " << I << "\n";
	if (callees.empty()) {
	  errs() << "\tno found callees\n";
	} else {
	  errs() << "\tpossible callees:\n";
	  for (unsigned i = 0, e = callees.size(); i < e; ++i) {
	    auto f = callees[i];
	    errs() << "\t\t" << cxx_demangle(f->getName().str()) << " "
		   << *(f->getType()) << "\n";
	  }
	}
      }
    }

    m_cha->printStats(errs());

    return false;
  }

  void getAnalysisUsage(AnalysisUsage &AU) const {
    AU.setPreservesAll();
  }

  const ClassHierarchyAnalysis& getCHA() const {
    return *m_cha;
  }
  
private:
  std::unique_ptr<ClassHierarchyAnalysis> m_cha;
};

char ClassHierarchyAnalysisPass::ID = 0;

llvm::Pass *createCHAPass() { return new ClassHierarchyAnalysisPass(); }

} // end namespace seahorn

static llvm::RegisterPass<seahorn::ClassHierarchyAnalysisPass>
    X("cha", "Class Hierarchy Analysis", false, false);
