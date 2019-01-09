#include "seahorn/Analysis/ClassHierarchyAnalysis.hh"

#include "seahorn/Support/SeaDebug.h"
#include "llvm/ADT/DenseMap.h"
#include "llvm/ADT/SmallSet.h"
#include "llvm/IR/CallSite.h"
#include "llvm/IR/Constants.h"
#include "llvm/IR/Module.h"
#include "llvm/IR/Value.h"
#include "llvm/Support/raw_ostream.h"

#include <boost/algorithm/string/find.hpp>
#include <boost/algorithm/string/predicate.hpp>
#include <cxxabi.h>

/*
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
   accessible by that class.

   1. For simple inheritance the vtable might look like this:

     class B {
        virtual int f1() = 0;
        virtual int f2(int) = 0;
        virtual int f3() { return 0;}
     };
     class D1: public B { ... }

     ;; vtable for D1
     @_ZTV2D1 = linkonce_odr unnamed_addr constant { [6 x i8*] }
     { [6 x i8*] [i8* null,
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

   3. For diamond inheritance the vtable my look like this:
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

   Second, the compiler adds a hidden pointer to the base class,
   which we will call _vptr_. Very importantly, vptr is inherited by
   derived classes. vptr is set (automatically) when a class object is
   created so that it points to the virtual table for that class.

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
  ClassHierarchyAnalysis_Impl(Module &Module) : m_module(Module) {}

  ~ClassHierarchyAnalysis_Impl() = default;

  void calculate(void);

  bool resolveVirtualCall(const llvm::ImmutableCallSite &CS,
                          std::vector<llvm::Function *> &out) const;

  void printVtables(raw_ostream &o) const;

  void printClassHierarchy(raw_ostream &o) const;

private:
  using graph_t =
      DenseMap<const StructType *, SmallSet<const StructType *, 16>>;
  using vtable_t = DenseMap<const StructType *, std::vector<Function *>>;

  Module &m_module;
  // -- class hierarchy graph (CHG)
  graph_t m_graph;
  // -- vtables
  vtable_t m_vtables;

  void buildCHG(void);

  void buildVtables(void);

  void closureCHG();

  void addVtableEntry(const StructType *ty, Function *fun);

  bool hasVtable(const StructType *ty) const;

  std::vector<Function *> &getVtable(const StructType *ty);

  const std::vector<Function *> &getVtable(const StructType *ty) const;

  void addCHGEdge(const StructType *src, const StructType *dest,
                  graph_t &graph);

  bool hasCHGEdge(const StructType *src, const StructType *dest,
                  graph_t &graph) const;

  void addCandidateFunction(const StructType *type, unsigned vtable_index,
                            const FunctionType *callsite_type,
                            SmallSet<Function *, 16> &out) const;

  static int extractVtableIndex(const ImmutableCallSite &CS);

  static bool matchVirtualSignature(const llvm::FunctionType *type_call,
                                    const llvm::FunctionType *type_candidate);
};

void ClassHierarchyAnalysis_Impl::addVtableEntry(const StructType *ty,
                                                 Function *fun) {
  auto it = m_vtables.find(ty);
  if (it != m_vtables.end()) {
    it->second.push_back(fun);
  } else {
    std::vector<Function *> funs;
    funs.push_back(fun);
    m_vtables.insert({ty, funs});
  }
}

bool ClassHierarchyAnalysis_Impl::hasVtable(const StructType *ty) const {
  return m_vtables.find(ty) != m_vtables.end();
}

std::vector<Function *> &
ClassHierarchyAnalysis_Impl::getVtable(const StructType *ty) {
  assert(hasVtable(ty));
  auto it = m_vtables.find(ty);
  return it->second;
}

const std::vector<Function *> &
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

int ClassHierarchyAnalysis_Impl::extractVtableIndex(
    const ImmutableCallSite &CS) {
  /*
    Assume the virtual call looks exactly like this:

     %33 = getelementptr inbounds i32 (%class.B*)*, i32 (%class.B*)** %32, i64 2
     %34 = load i32 (%class.B*)*, i32 (%class.B*)** %33, align 8
     %35 = call i32 %34(%class.B* %30)

   */
  if (const LoadInst *LI = dyn_cast<LoadInst>(CS.getCalledValue())) {
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
      }
    }
  }
  std::swap(m_graph, closed_g);
}

void ClassHierarchyAnalysis_Impl::buildCHG(void) {
  // The construction of the class hierarchy graph is currently too
  // rough. For instance, in cases like this
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
  }
  for (auto st : struct_types) {
    for (auto sub_ty : st->subtypes()) {
      if (const StructType *sub_st_ty = dyn_cast<const StructType>(sub_ty)) {
        addCHGEdge(sub_st_ty, st, m_graph);
      }
    }
  }
}

void ClassHierarchyAnalysis_Impl::buildVtables(void) {

  const static std::string vtable_for_str = "vtable for";
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

    /*
      XXX: from Phasar.

      The goal is to associate a class with its vtable. It tries to
      find the constructor of the class by searching for the
      instruction that sets vptr via an store. If it finds the
      constructor, the class is obtained from the argument to the
      constructor.

      This is how the constructor for class D1 might look like:

      define linkonce_odr void @_ZN2D1C2Ev(%class.D1*) unnamed_addr #3 align 2 {
         %2 = alloca %class.D1*, align 8
         store %class.D1* %0, %class.D1** %2, align 8
         %3 = load %class.D1*, %class.D1** %2, align 8
         %4 = bitcast %class.D1* %3 to %class.B*
         ;;; B::B()
         call void @_ZN1BC2Ev(%class.B* %4)
         %5 = bitcast %class.D1* %3 to i32 (...)***
         store i32 (...)**
               bitcast (i8** getelementptr inbounds ({[6 x i8*]}, {[6 x i8*]}*
               @_ZTV2D1, i32 0, inrange i32 0, i32 2) to i32 (...)**), i32
      (...)*** %5 ret void
      }

      Here, we would like to associate %class.D1* with @_ZTV2D1 (the
      vtable for D1).

      XXX: if the class inherits from multiple classes will have
           multiple store ( bitcast( getelementptr( ....) ...) ...)
           instructions.
    */

    if (gv.user_empty()) {
      LOG("cha",
          errs() << "The vtable " << demangled_gv_name << " has no users\n";);
      continue;
    }

    // (from phasar): quite ad-hoc syntactic approach. It works only
    // if the constructor is not inlined. It also relies on the order
    // of a Value's users.
    //
    // The first use return a ConstExpr (GetElementPtr) inside a
    // ConstExpr (Bitcast) inside a store We need to access directly
    // the store as the ConstExpr are not linked to a basic block and
    // so they can not be printed, we can not access the function in
    // which they are directly, ...
    auto base = gv.user_begin();
    while (base != gv.user_end() &&
           (base->user_empty() || base->user_begin()->user_empty() ||
            isa<Constant>(*(base->user_begin()->user_begin())))) {
      ++base;
    }

    if (base == gv.user_end()) {
      continue;
    }

    // Find the constructor where vptr is initialized
    auto store_vtable_inst =
        dyn_cast<StoreInst>(*(base->user_begin()->user_begin()));
    if (!store_vtable_inst) {
      LOG("cha", errs() << "Cannot find the store instruction that initializes "
                           "the vtable\n";);
      continue;
    }
    Function *constructor = store_vtable_inst->getFunction();
    if (!constructor) {
      LOG("cha", errs() << "Cannot find function associated with "
                        << *store_vtable_inst << "\n";);
      continue;
    }

    if (constructor->arg_size() == 0) {
      LOG("cha",
          errs()
              << "What we thought was a constructor is not a constructor\n";);
      continue;
    }

    // We get the type of "this" (the first argument of the constructor)
    Argument &this_ = *(constructor->arg_begin());

    const StructType *this_type =
        dyn_cast<const StructType>(getNonPointerType(this_.getType()));
    if (!this_type) {
      LOG("cha", errs() << "Cannot get type of this "
                        << *(getNonPointerType(this_.getType())) << "\n";);
      continue;
    }

    // At this point, `this_type` is the StructType of the class.
    // Get all the functions from the vtable
    Constant *gv_initializer = gv.getInitializer();
    for (unsigned i = 0, e = gv_initializer->getNumOperands(); i < e; ++i) {
      if (ConstantArray *CA =
              dyn_cast<ConstantArray>(gv_initializer->getAggregateElement(i))) {
        for (unsigned j = 0; j < CA->getNumOperands(); ++j) {
          if (ConstantExpr *CE =
                  dyn_cast<ConstantExpr>(CA->getAggregateElement(j))) {
            if (CE->isCast()) {
              if (Constant *Cast =
                      ConstantExpr::getBitCast(CE, CE->getType())) {
                if (Function *VF = dyn_cast<Function>(Cast->getOperand(0))) {
                  addVtableEntry(this_type, VF);
                }
              }
            }
          }
        }
      }
    }

  } // end outer loop
}

void ClassHierarchyAnalysis_Impl::calculate() {
  buildCHG();
  buildVtables();
  closureCHG();
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
    auto &callees = getVtable(type);
    if (vtable_index < callees.size()) {
      Function *callee = callees[vtable_index];
      if (matchVirtualSignature(callsite_type, callee->getFunctionType())) {
        out.insert(callees[vtable_index]);
      } else {
        // LOG("cha", errs() << "Candidate callee type does not match "
        //                   << "virtual call type\n";);
      }
    } else {
      LOG("cha", errs() << "The vtable index is out-of-bounds\n";);
    }
  }
}

bool ClassHierarchyAnalysis_Impl::resolveVirtualCall(
    const ImmutableCallSite &CS, std::vector<Function *> &out) const {
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

      int vtable_index = extractVtableIndex(CS);
      if (vtable_index < 0) {
        LOG("cha", errs() << "Cannot resolve " << *(CS.getInstruction()) << ": "
                          << "cannot find vtable index for indirect call "
                          << *CS.getInstruction() << "\n";);
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
      return true;
    }
  }

  LOG("cha", errs() << "Cannot resolve virtual call " << *CS.getInstruction()
                    << " because first argument is not StructType\n";);

  return false;
}

void ClassHierarchyAnalysis_Impl::printVtables(raw_ostream &o) const {
  for (auto &kv : m_vtables) {
    const StructType *class_ty = kv.first;
    auto const &funs = kv.second;
    o << cxx_demangle(class_ty->getName().str()) << ":\n";
    for (Function *f : funs) {
      o << "\t" << cxx_demangle(f->getName().str()) << " " << *(f->getType())
        << "\n";
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

/** ClassHierarchyAnalysis methods **/
ClassHierarchyAnalysis::ClassHierarchyAnalysis(Module &M)
    : m_cha_impl(new ClassHierarchyAnalysis_Impl(M)) {}

ClassHierarchyAnalysis::~ClassHierarchyAnalysis() {
  if (m_cha_impl) {
    delete m_cha_impl;
  }
}

void ClassHierarchyAnalysis::calculate(void) {
  m_cha_impl->calculate();
}

bool ClassHierarchyAnalysis::resolveVirtualCall(
    const ImmutableCallSite &CS, std::vector<Function *> &out) const {
  return m_cha_impl->resolveVirtualCall(CS, out);
}

void ClassHierarchyAnalysis::printClassHierarchy(raw_ostream &o) const {
  m_cha_impl->printClassHierarchy(o);
}

void ClassHierarchyAnalysis::printVtables(raw_ostream &o) const {
  m_cha_impl->printVtables(o);
}

/** LLVM pass **/
class ClassHierarchyAnalysisPass : public ModulePass {
public:
  static char ID;

  ClassHierarchyAnalysisPass() : ModulePass(ID), m_cha(nullptr) {}

  ~ClassHierarchyAnalysisPass() {
    if (m_cha) {
      delete m_cha;
    }
  }

  bool runOnModule(Module &M) {
    m_cha = new ClassHierarchyAnalysis(M);
    m_cha->calculate();

    LOG("cha", errs() << "===================\n";
        errs() << "       CHA         \n"; errs() << "===================\n";
        m_cha->printClassHierarchy(errs()); errs() << "\n";
        errs() << "==================\n"; errs() << "     Vtables      \n";
        errs() << "==================\n"; m_cha->printVtables(errs());
        errs() << "==================\n"; errs() << " Devirtualization \n";
        errs() << "==================\n";

        for (auto &F
             : M) {
          for (auto &BB : F) {
            for (auto &I : BB) {
              if (isa<CallInst>(I) || isa<InvokeInst>(I)) {
                ImmutableCallSite CS(&I);
                std::vector<Function *> callees;
                if (m_cha->resolveVirtualCall(CS, callees)) {
                  errs() << "Found virtual call " << I << "\n";
                  if (callees.empty()) {
                    errs() << "No found callees\n";
                  } else {
                    errs() << "Possible callees:\n";
                    for (unsigned i = 0, e = callees.size(); i < e; ++i) {
                      auto f = callees[i];
                      errs() << "\t" << cxx_demangle(f->getName().str()) << " "
                             << *(f->getType()) << "\n";
                    }
                  }
                }
              }
            }
          }
        });

    return false;
  }

  void getAnalysisUsage(AnalysisUsage &AU) const { AU.setPreservesAll(); }

  bool resolveVirtualCall(const ImmutableCallSite &CS,
                          std::vector<Function *> &out) {
    return m_cha->resolveVirtualCall(CS, out);
  }

private:
  ClassHierarchyAnalysis *m_cha;
};

char ClassHierarchyAnalysisPass::ID = 0;

llvm::Pass *createCHAPass() { return new ClassHierarchyAnalysisPass(); }

} // end namespace seahorn

static llvm::RegisterPass<seahorn::ClassHierarchyAnalysisPass>
    X("cha", "Class Hierarchy Analysis", false, false);
