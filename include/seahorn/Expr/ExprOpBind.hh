/// Bind things together
#pragma once

#include "seahorn/Expr/ExprApi.hh"
#include "seahorn/Expr/ExprCore.hh"
#include "seahorn/Expr/ExprOpCore.hh"

#include "seahorn/Expr/ExprOpBool.hh"
#include "seahorn/Expr/ExprOpSort.hh"
#include "seahorn/Expr/ExprOpVariant.hh"

namespace expr {

namespace op {

namespace bind {
struct SCOPE_PS {
  static inline void print(std::ostream &OS, int depth, bool brkt,
                           const std::string &name,
                           const std::vector<ENode *> &args) {
    OS << "[" << name << " ";
    args[0]->Print(OS, depth + 2, false);
    OS << " in ";
    args[1]->Print(OS, depth + 2, false);
    OS << "]";
  }
};
struct FAPP_PS;
} // namespace bind
enum class BindOpKind { BIND, FDECL, FAPP };
NOP_BASE(BindOp)

NOP(BIND, ":", INFIX, BindOp)
/** Function declaration */
NOP(FDECL, "fdecl", PREFIX, BindOp)
/** Function application */
NOP(FAPP, "fapp", bind::FAPP_PS, BindOp)

namespace bind {
inline Expr bind(Expr name, Expr value) { return mk<BIND>(name, value); }
inline Expr name(Expr e) { return e->left(); }
inline Expr type(Expr e) { return e->right(); }
inline Expr value(Expr e) { return e->right(); }

inline Expr var(Expr name, Expr type) { return bind(name, type); }
inline Expr intVar(Expr name) { return var(name, mk<INT_TY>(name->efac())); }
inline Expr realVar(Expr name) { return var(name, mk<REAL_TY>(name->efac())); }
inline Expr boolVar(Expr name) { return var(name, mk<BOOL_TY>(name->efac())); }
inline Expr charVar(Expr name) { return var(name, mk<CHAR_TY>(name->efac())); }
inline Expr unintVar(Expr name) {
  return var(name, mk<UNINT_TY>(name->efac()));
}

template <typename T> bool isVar(Expr v) {
  return isOpX<BIND>(v) && isOpX<T>(bind::type(v));
}
inline bool isBoolVar(Expr v) { return isVar<BOOL_TY>(v); }
inline bool isIntVar(Expr v) { return isVar<INT_TY>(v); }
inline bool isRealVar(Expr v) { return isVar<REAL_TY>(v); }

inline Expr constDecl(Expr name, Expr type) { return mk<FDECL>(name, type); }
inline Expr boolConstDecl(Expr name) {
  return constDecl(name, mk<BOOL_TY>(name->efac()));
}
inline Expr intConstDecl(Expr name) {
  return constDecl(name, mk<INT_TY>(name->efac()));
}
inline Expr realConstDecl(Expr name) {
  return constDecl(name, mk<REAL_TY>(name->efac()));
}

template <typename Range> Expr fdecl(Expr fname, const Range &args) {
  // -- at least one value for range type
  assert(boost::size(args) > 0);
  ExprVector _args;
  _args.push_back(fname);
  _args.insert(_args.end(), std::begin(args), std::end(args));
  return mknary<FDECL>(_args);
}

inline bool isFdecl(Expr fdecl) { return isOpX<FDECL>(fdecl); }
inline Expr fname(Expr fdecl) { return fdecl->first(); }

inline Expr fapp(Expr fdecl) { return mk<FAPP>(fdecl); }

template <typename Range> Expr fapp(Expr fdecl, const Range &args) {
  ExprVector _args;
  _args.push_back(fdecl);
  _args.insert(_args.end(), std::begin(args), std::end(args));
  return mknary<FAPP>(_args);
}

inline Expr fapp(Expr fdecl, Expr a0, Expr a1 = Expr(), Expr a2 = Expr()) {
  ExprVector args;
  args.push_back(fdecl);

  if (a0)
    args.push_back(a0);
  if (a1)
    args.push_back(a1);
  if (a2)
    args.push_back(a2);
  return mknary<FAPP>(args);
}

inline bool isFapp(Expr fapp) { return isOpX<FAPP>(fapp); }

inline Expr rangeTy(Expr fdecl) { return fdecl->last(); }

inline size_t domainSz(Expr fdecl) {
  assert(fdecl->arity() >= 2);
  return fdecl->arity() - 2;
}

inline Expr domainTy(Expr fdecl, size_t n) {
  assert(n + 2 < fdecl->arity());
  return fdecl->arg(n + 1);
}

template <typename T> bool isFdecl(Expr v) {
  return isOpX<FDECL>(v) && isOpX<T>(rangeTy(v));
}

/** constant is an applied nullary function */
template <typename T> bool isConst(Expr v) {
  return isOpX<FAPP>(v) && v->arity() == 1 && isFdecl<T>(fname(v));
}

inline Expr mkConst(Expr name, Expr sort) {
  return fapp(constDecl(name, sort));
}
inline Expr boolConst(Expr name) { return fapp(boolConstDecl(name)); }
inline Expr intConst(Expr name) { return fapp(intConstDecl(name)); }
inline Expr realConst(Expr name) { return fapp(realConstDecl(name)); }

inline bool isBoolConst(Expr v) { return isConst<BOOL_TY>(v); }
inline bool isIntConst(Expr v) { return isConst<INT_TY>(v); }
inline bool isRealConst(Expr v) { return isConst<REAL_TY>(v); }
inline bool isArrayConst(Expr v) { return isConst<ARRAY_TY>(v); }
inline bool isStructConst(Expr v) { return isConst<STRUCT_TY>(v);}
inline bool isFiniteMapConst(Expr v) { return isConst<FINITE_MAP_TY>(v); }

inline Expr typeOf(Expr v) {
  using namespace bind;
  if (isOpX<VARIANT>(v))
    return typeOf(variant::mainVariant(v));

  if (isOpX<FAPP>(v)) {
    assert(isOpX<FDECL>(v->left()));
    return rangeTy(v->left());
  }

  if (isOpX<TRUE>(v) || isOpX<FALSE>(v))
    return mk<BOOL_TY>(v->efac());
  if (isOpX<MPZ>(v))
    return mk<INT_TY>(v->efac());
  if (isOpX<MPQ>(v))
    return mk<REAL_TY>(v->efac());

  if (isOpX<BIND>(v))
    return bind::type(v);

  if (isBoolVar(v) || isBoolConst(v))
    return mk<BOOL_TY>(v->efac());
  if (isIntVar(v) || isIntConst(v))
    return mk<INT_TY>(v->efac());
  if (isRealVar(v) || isRealConst(v))
    return mk<REAL_TY>(v->efac());

  if (isOpX<SELECT>(v)) {
    Expr a = v->left();
    if (isOpX<FAPP>(a)) {
      Expr decl_a = a->left(); // decl_a is fdecl name (ARRAY idxTy valTy)
      Expr array_ty = decl_a->right();
      Expr val_ty = array_ty->right();
      return val_ty;
    }
  }

  // if (isOpX<STORE>(v)) {
  //   Expr a = v->left();
  //   if (isOpX<FAPP> (a)) {
  //     Expr decl_a = a->left(); // decl_a is fdecl name (ARRAY idxTy valTy)
  //     Expr array_ty = decl_a->right();
  //     return array_ty;
  //   }
  // }

  std::cerr << "WARNING: could not infer type of: " << *v << "\n";
  llvm_unreachable("Type inference failed");
  return Expr();
}
inline Expr sortOf(Expr v) { return typeOf(v); }

struct FAPP_PS {
  static inline void print(std::ostream &OS, int depth, int brkt,
                           const std::string &name,
                           const std::vector<ENode *> &args) {
    if (args.size() > 1)
      OS << "(";

    // -- strip fdecl if there is one
    ENode *fname = args[0];
    if (isOpX<FDECL>(fname))
      fname = fname->arg(0);
    fname->Print(OS, depth + 2, false);

    for (unsigned i = 1; i < args.size(); ++i) {
      OS << " ";
      args[i]->Print(OS, depth + 2, false);
    }

    if (args.size() > 1)
      OS << ")";
  }
};

/// Creates a new fdecl with the same signature as the given
/// fdecl and a new name
inline Expr rename(Expr fdecl, Expr name) {
  assert(isOpX<FDECL>(fdecl));
  ExprVector _args;
  _args.reserve(fdecl->arity());
  _args.push_back(name);
  _args.insert(_args.end(), ++(fdecl->args_begin()), fdecl->args_end());
  return mknary<FDECL>(_args);
}

/// construct a new expression by applying fdecl to the same
/// arguments as fapp. For example, reapp of g(a,b) and f is f(a, b)
inline Expr reapp(Expr fapp, Expr fdecl) {
  assert(isOpX<FDECL>(fdecl));
  assert(isOpX<FAPP>(fapp));

  ExprVector _args;
  _args.reserve(fapp->arity());
  _args.push_back(fdecl);
  _args.insert(_args.end(), ++(fapp->args_begin()), fapp->args_end());
  return mknary<FAPP>(_args);
}
} // namespace bind

namespace bind {
/// returns true if an expression is a constant
class IsConst : public std::unary_function<Expr, bool> {
public:
  bool operator()(Expr e) {
    if (isOpX<VARIANT>(e))
      return this->operator()(variant::mainVariant(e));

    return isOpX<FAPP>(e) && e->arity() == 1 && isOpX<FDECL>(fname(e));
  }
};
} // namespace bind
} // namespace op

} // namespace expr
