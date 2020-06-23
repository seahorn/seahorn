/// Core operators and temrinals
#pragma once
#include "seahorn/Expr/ExprCore.hh"
#include "seahorn/Expr/ExprGmp.hh"
#include "llvm/Support/Casting.h"

namespace expr {

class TypeCheckertc;
namespace op {
namespace typeCheck {
struct Any;
} // namespace typeCheck
namespace sort {
Expr stringTerminalTy(ExprFactory &efac);
Expr intTy(ExprFactory &efac);
Expr realTy(ExprFactory &efac);
} // namespace sort
} // namespace op

/// \brief A trait that must be impelemnted by a type \ T to be a terminal
/// see example specializations below
template <typename T> struct TerminalTrait {};

/// \brief Terminal kinds
/// Each terminal must register itself in this enum class
enum class TerminalKind {
  // C++ std::strings
  STRING,
  // unsigned int
  UINT,
  // GMP rational
  MPQ,
  // GMP integer
  MPZ,
  // Bounded / quantified variable
  BVAR,
  // Bit-vector sort
  BVSORT,
  // llvm::Value
  LLVM_VALUE,
  // llvm::BasicBlock
  LLVM_BASICBLOCK,
  // llvm::Function
  LLVM_FUNCTION
};

// \brief Base class for implementing a Terminal
struct TerminalBase : public expr::Operator {
  TerminalKind m_kind;
  TerminalBase(TerminalKind k)
      : Operator(expr::OpFamilyId::Terminal), m_kind(k) {}

  static bool classof(Operator const *op) {
    return op->getFamilyId() == expr::OpFamilyId::Terminal;
  }
};

/// \brief Terminal Operator
/// \p T is the type wrapped by the terminal, and \p P is the implementation of
/// terminal traits for \p T
template <typename T, typename P = TerminalTrait<T>>
class Terminal : public TerminalBase {
protected:
  T val;

public:
  using base_type = T;
  using terminal_type = P;
  using this_type = Terminal<T, P>;

  Terminal(const base_type &v)
      : TerminalBase(terminal_type::getKind()), val(v) {}

  base_type get() const { return val; }

  this_type *clone(ExprFactoryAllocator &allocator) const override {
    return new (allocator) this_type(val);
  }

  void Print(std::ostream &OS, const std::vector<ENode *> &args, int depth = 0,
             bool brkt = true) const override {
    terminal_type::print(OS, val, depth, brkt);
  }

  std::string name() const { return terminal_type::name(); }

  bool operator==(const this_type &rhs) const {
    return terminal_type::equal_to(val, rhs.val);
  }

  bool operator<(const this_type &rhs) const {
    return terminal_type::less(val, rhs.val);
  }

  bool operator==(const Operator &rhs) const override {
    if (&rhs == this)
      return true;

    auto *prhs = llvm::dyn_cast<this_type>(&rhs);
    return prhs && terminal_type::equal_to(val, prhs->val);
  }

  bool operator<(const Operator &rhs) const override {
    // x < x is false
    if (&rhs == this)
      return false;

    if (this->getFamilyId() != rhs.getFamilyId())
      return this->getFamilyId() < rhs.getFamilyId();

    // rhs is a Terminal

    // check if rhs is this_type
    auto *prhs = llvm::dyn_cast<this_type>(&rhs);

    // use terminal trait defined less
    if (prhs)
      return terminal_type::less(val, prhs->val);
    // order based on kinds
    return terminal_type::getKind() < llvm::cast<TerminalBase>(&rhs)->m_kind;
  }

  size_t hash() const override { return terminal_type::hash(val); }

  static bool classof(Operator const *op) {
    return llvm::isa<TerminalBase>(op) &&
           llvm::cast<TerminalBase>(op)->m_kind == terminal_type::getKind();
  }

  Expr inferType(Expr exp, TypeChecker &tc) const override {
    return terminal_type::inferType(exp, tc);
  }
};

/// \brief Terminal traits for std::string
template <> struct TerminalTrait<std::string> {
  static inline void print(std::ostream &OS, const std::string &s, int depth,
                           bool brkt) {
    OS << s;
  }
  static inline bool less(const std::string &s1, const std::string &s2) {
    return s1 < s2;
  }
  static inline bool equal_to(const std::string &s1, const std::string &s2) {
    return s1 == s2;
  }
  static inline size_t hash(const std::string &s) {
    std::hash<std::string> hasher;
    return hasher(s);
  }
  static TerminalKind getKind() { return TerminalKind::STRING; }
  static std::string name() { return "std::string"; }
  static inline Expr inferType(Expr exp, TypeChecker &tc) {
    return sort::stringTerminalTy(exp->efac());
  }
};

/// \brief Terminal traits for unsigned int
template <> struct TerminalTrait<unsigned int> {
  static inline void print(std::ostream &OS, unsigned int s, int depth,
                           bool brkt) {
    OS << s;
  }
  static inline bool less(const unsigned int &i1, const unsigned int &i2) {
    return i1 < i2;
  }
  static inline bool equal_to(unsigned int i1, unsigned int i2) {
    return i1 == i2;
  }
  static inline size_t hash(unsigned int i) {
    std::hash<unsigned int> hasher;
    return hasher(i);
  }
  static TerminalKind getKind() { return TerminalKind::UINT; }
  static std::string name() { return "unsigned int"; }
  static inline Expr inferType(Expr exp, TypeChecker &tc) {
    return sort::intTy(exp->efac());
  }
};

/// \brief Termianl traits for GMP integers
template <> struct TerminalTrait<expr::mpz_class> {
  static inline void print(std::ostream &OS, const expr::mpz_class &v,
                           int depth, bool brkt) {
    /* print large numbers in hex */
    if (v >= 65535UL || v <= -65535L)
      OS << "0x" << v.to_string(16);
    else
      OS << v.to_string(10);
  }

  static inline bool less(const expr::mpz_class &v1,
                          const expr::mpz_class &v2) {
    return v1 < v2;
  }

  static inline bool equal_to(const expr::mpz_class &v1,
                              const expr::mpz_class &v2) {
    return v1 == v2;
  }

  static inline size_t hash(const expr::mpz_class &v) {
    std::hash<std::string> hasher;
    return hasher(v.to_string());
  }

  static TerminalKind getKind() { return TerminalKind::MPZ; }
  static std::string name() { return "expr::mpz_class"; }
  static inline Expr inferType(Expr exp, TypeChecker &tc) {
    return sort::intTy(exp->efac());
  }
};

/// \brief Terminal traits for GMP rationals
template <> struct TerminalTrait<expr::mpq_class> {
  static inline void print(std::ostream &OS, const expr::mpq_class &v,
                           int depth, bool brkt) {
    OS << v.to_string();
  }

  static inline bool less(const expr::mpq_class &v1,
                          const expr::mpq_class &v2) {
    return v1 < v2;
  }

  static inline bool equal_to(const expr::mpq_class &v1,
                              const expr::mpq_class &v2) {
    return v1 == v2;
  }

  static inline size_t hash(const expr::mpq_class &v) {
    std::hash<std::string> hasher;
    return hasher(v.to_string());
  }

  static TerminalKind getKind() { return TerminalKind::MPQ; }
  static std::string name() { return "expr::mpq_class"; }
  static inline Expr inferType(Expr exp, TypeChecker &tc) {
    return sort::realTy(exp->efac());
  }
};

// Define concise names for terminal operators
namespace op {
using STRING = Terminal<std::string>;
using UINT = Terminal<unsigned int>;
using MPQ = Terminal<expr::mpq_class>;
using MPZ = Terminal<expr::mpz_class>;
} // namespace op

// Functions for printing operators
namespace ps {

/// \brief print \p c spaces
inline std::ostream &space(std::ostream &OS, size_t c) {
  for (size_t i = 0; i < c; i++)
    OS << " ";
  return OS;
}

/// \brief Prefix printing trait
struct PREFIX {
  static inline void print(std::ostream &OS, int depth, bool brkt,
                           const std::string &name,
                           const std::vector<ENode *> &args) {
    if (args.size() >= 2)
      OS << "[";
    if (args.size() == 1 && brkt)
      OS << "(";

    OS << name;
    if (args.empty())
      return;

    if (args.size() == 1) {
      // OS << " ";
      args[0]->Print(OS, depth + 2, true);
      if (brkt)
        OS << ")";
      return;
    }

    for (std::vector<ENode *>::const_iterator it = args.begin(),
                                              end = args.end();
         it != end; ++it) {
      OS << "\n";
      space(OS, depth + 2);
      (*it)->Print(OS, depth + 2, false);
    }

    OS << "\n";
    space(OS, depth);
    OS << "]";
  }
};

/// \brief Infix printing trait
struct INFIX {
  static inline void print(std::ostream &OS, int depth, bool brkt,
                           const std::string &name,
                           const std::vector<ENode *> &args) {

    if (args.size() != 2) {
      PREFIX::print(OS, depth, brkt, name, args);
      return;
    }

    if (brkt)
      OS << "(";
    args[0]->Print(OS, depth, true);
    OS << name;
    args[1]->Print(OS, depth, true);
    if (brkt)
      OS << ")";
  }
};

/// \brief Functional printing trait
struct FUNCTIONAL {
  static inline void print(std::ostream &OS, int depth, bool brkt,
                           const std::string &name,
                           const std::vector<ENode *> &args) {
    OS << name << "(";

    bool first = true;
    for (std::vector<ENode *>::const_iterator it = args.begin(),
                                              end = args.end();
         it != end; ++it) {
      if (!first)
        OS << ", ";
      (*it)->Print(OS, depth + 2, false);
      first = false;
    }

    OS << ")";
  }
};

/// \brief Lisp printing trait
struct LISP {
  static inline void print(std::ostream &OS, int depth, bool brkt,
                           const std::string &name,
                           const std::vector<ENode *> &args) {
    OS << "(" << name << " ";

    bool first = true;
    for (std::vector<ENode *>::const_iterator it = args.begin(),
                                              end = args.end();
         it != end; ++it) {
      if (!first)
        OS << " ";
      (*it)->Print(OS, depth + 2, true);
      first = false;
    }

    OS << ")";
  }
};

/// \brief Address printing trait
struct ADDRESS {
  static inline void print(std::ostream &OS, int depth, bool brkt,
                           const std::string &name,
                           const std::vector<ENode *> &args) {
    assert(args.size() == 1);
    OS << name << "!" << args.at(0)->getId();
  }
};
} // namespace ps

using namespace ps;

/// \brief Base class for an Operator implementation
/// \p T is the type of the operator
/// \p B is the base class
/// \p K is the kind for custom RTTI
template <typename T, typename B, typename P, typename K, K kind, typename C>
struct DefOp : public B {
  using this_type = DefOp<T, B, P, K, kind, C>;
  using kind_type = K;
  using base_type = B;
  using op_type = T;
  using ps_type = P;
  using checker_type = C;

  DefOp() : B(kind) {}
  DefOp(DefOp const &) = default;

  void Print(std::ostream &OS, const std::vector<ENode *> &args, int depth = 0,
             bool brkt = true) const override {
    ps_type::print(OS, depth, brkt, op_type::name(), args);
  }

  std::string name() const override { return op_type::name(); }

  bool operator==(const Operator &rhs) const override {
    if (this == &rhs)
      return true;
    auto *prhs = llvm::dyn_cast<this_type>(&rhs);
    return prhs && prhs->m_kind == kind;
  }

  bool operator<(const Operator &rhs) const override {
    if (rhs.getFamilyId() != this->getFamilyId())
      return this->getFamilyId() < rhs.getFamilyId();

    return kind < llvm::cast<base_type>(&rhs)->m_kind;
  }

  size_t hash() const override {
    std::size_t seed = 0;
    boost::hash_combine(seed, this->getFamilyId());
    boost::hash_combine(seed, kind);
    return seed;
  }

  this_type *clone(ExprFactoryAllocator &allocator) const override {
    return new (allocator) this_type(*this);
  }

  static bool classof(Operator const *op) {
    return llvm::isa<base_type>(op) &&
           llvm::cast<base_type>(op)->m_kind == kind;
  }

  Expr inferType(Expr exp, TypeChecker &tc) const override {
    return checker_type::inferType(exp, tc);
  }
};

} // namespace expr

/// macro for defining base class for operator hierarchy
#define NOP_BASE(NAME)                                                         \
  struct NAME : public expr::Operator {                                        \
    NAME##Kind m_kind;                                                         \
    NAME(NAME##Kind k) : Operator(expr::OpFamilyId::NAME), m_kind(k) {}        \
    static bool classof(const Operator *op) {                                  \
      return op->getFamilyId() == expr::OpFamilyId::NAME;                      \
    }                                                                          \
  };

/// macro for defining a class for a single operator
#define NOP(NAME, TEXT, STYLE, BASE, TYPECHECK)                                \
  struct __##NAME {                                                            \
    static inline std::string name() { return TEXT; }                          \
  };                                                                           \
  using NAME =                                                                 \
      DefOp<__##NAME, BASE, STYLE, BASE##Kind, BASE##Kind::NAME, TYPECHECK>;
