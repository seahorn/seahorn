/**
   Define tabular function interpretation
*/
#ifndef _EXPR_INTERP__H_
#define _EXPR_INTERP__H_

#include "seahorn/Expr/Expr.hh"

namespace expr {
namespace op {
enum class MutModelOpKind { FTABLE, FENTRY };
struct MutModelOp : public expr::Operator {
  MutModelOpKind m_kind;
  MutModelOp(MutModelOpKind k) : Operator(expr::OpFamilyId::MutModelOp), m_kind(k) {}
  virtual bool isMutable() const { return true; }
  static bool classof(expr::Operator const *op) {
    return op->getFamilyId() == expr::OpFamilyId::MutModelOp;
  }
};

namespace mdl {
struct FTAB_PS {
  static inline void print(std::ostream &OS, int depth, bool brkt,
                           const std::string &name,
                           const std::vector<ENode *> &args) {
    OS << "[";
    unsigned sz = args.size();
    assert(sz > 0);

    for (unsigned i = 0; i < sz - 1; ++i) {
      args[i]->Print(OS, depth, false);
      if (i + 1 < sz - 1)
        OS << " | ";
    }

    if (sz > 1)
      OS << " | ";
    OS << "else -> ";
    args[sz - 1]->Print(OS, depth, false);
    OS << "]";
  }
};

struct FENT_PS {
  static inline void print(std::ostream &OS, int depth, bool brkt,
                           const std::string &name,
                           const std::vector<ENode *> &args) {

    if (args.size() == 1)
      args[0]->Print(OS, depth, false);
    else {
      unsigned sz = args.size();
      assert(sz > 0);
      if (sz > 2)
        OS << "(";
      for (unsigned i = 0; i < sz - 1; ++i) {
        args[i]->Print(OS, depth, false);
        if (i + 1 < sz - 1)
          OS << ", ";
      }

      if (sz > 2)
        OS << ")";
      OS << "->";
      args[sz - 1]->Print(OS, depth, false);
    }
  }
};
} // namespace mdl

NOP(FTABLE, "ftab", mdl::FTAB_PS, MutModelOp);
NOP(FENTRY, "fent", mdl::FENT_PS, MutModelOp);

namespace mdl {
template <typename Range> Expr fentry(const Range &args, Expr value) {
  ExprVector _args(std::begin(args), std::end(args));
  assert(value);
  _args.push_back(value);

  return mknary<FENTRY>(_args);
}

inline unsigned fentryArity(Expr fentry) { return fentry->arity() - 1; }
inline Expr fentryArg(Expr fentry, unsigned entry) {
  return fentry->arg(entry);
}
inline Expr fentryVal(Expr fentry) { return fentry->arg(fentry->arity() - 1); }

template <typename Range> Expr ftable(const Range &entries, Expr value) {
  ExprVector _args(std::begin(entries), std::end(entries));
  assert(value);
  _args.push_back(value);

  return mknary<FTABLE>(_args);
}
inline unsigned ftableEntries(Expr ftable) { return ftable->arity() - 1; }
inline Expr ftableEntry(Expr ftable, unsigned i) { return ftable->arg(i); }
inline Expr ftableElseV(Expr ftable) {
  return ftable->arg(ftable->arity() - 1);
}
} // namespace mdl
} // namespace op
} // namespace expr

#endif /* _EXPR_INTERP__H_ */
