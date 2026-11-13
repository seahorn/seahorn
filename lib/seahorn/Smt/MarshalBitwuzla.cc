#ifdef WITH_BITWUZLA

#include "seahorn/Expr/Smt/MarshalBitwuzla.hh"
#include "seahorn/Expr/ExprLlvm.hh"
#include "seahorn/Expr/ExprOpBinder.hh"

#include "llvm/Support/Casting.h"
#include "llvm/Support/raw_ostream.h"

#include "boost/lexical_cast.hpp"

#include <algorithm>
#include <cassert>
#include <gmp.h>
#include <utility>

using namespace expr;
using bitwuzla::Kind;
using bitwuzla::Sort;
using bitwuzla::Term;

namespace seahorn {
namespace solver {

/// \p e printed as a tree has at most \p budget nodes
static bool isSmall(Expr e, unsigned &budget) {
  if (budget == 0)
    return false;
  --budget;
  for (unsigned i = 0, sz = e->arity(); i < sz; ++i)
    if (!isSmall(e->arg(i), budget))
      return false;
  return true;
}

/// Prints \p e if it is small, and otherwise only its operator and its small
/// arguments. Printing a large DAG as a tree can take exponential time.
static void printShort(llvm::raw_ostream &os, Expr e) {
  unsigned budget = 16;
  if (isSmall(e, budget)) {
    os << *e;
    return;
  }
  const unsigned max_args = 4;
  os << e->op().name() << "(";
  for (unsigned i = 0, sz = e->arity(); i < sz && i < max_args; ++i) {
    if (i > 0)
      os << ", ";
    budget = 8;
    if (isSmall(e->arg(i), budget))
      os << *e->arg(i);
    else
      os << e->arg(i)->op().name() << "(...)";
  }
  if (e->arity() > max_args)
    os << ", ...";
  os << ")";
}

static std::string describe(Expr e, const std::string &reason) {
  std::string str;
  llvm::raw_string_ostream os(str);
  printShort(os, e);
  os.flush();
  return reason + ": " + str;
}

UnsupportedExpr::UnsupportedExpr(Expr e, const std::string &reason)
    : std::runtime_error(describe(e, reason)), m_expr(e) {}

static std::string get_name(Expr fdecl) {
  Expr fname = bind::fname(fdecl);
  if (isOpX<STRING>(fname))
    return getTerm<std::string>(fname);
  return boost::lexical_cast<std::string>(*fname);
}

static bool isBinder(Expr e) {
  return isOpX<LAMBDA>(e) || isOpX<FORALL>(e) || isOpX<EXISTS>(e);
}

/// Exprs that are encoded without encoding any children first: Boolean
/// values, numerals and bound variables (BIND), and constants (FAPP of a
/// declaration alone)
static bool isLeaf(Expr e) {
  return e->arity() == 0 || isOpX<BIND>(e) ||
         (bind::isFapp(e) && e->arity() == 1);
}

/// The Bitwuzla kind for the operator of \p e. Throws UnsupportedExpr for
/// an operator the encoder does not support.
static Kind kindOf(Expr e) {
  switch (e->op().getFamilyId()) {
  case OpFamilyId::BoolOp:
    switch (llvm::cast<BoolOp>(e->op()).m_kind) {
    case BoolOpKind::AND:
      return Kind::AND;
    case BoolOpKind::OR:
      return Kind::OR;
    case BoolOpKind::XOR:
      return Kind::XOR;
    case BoolOpKind::NEG:
      return Kind::NOT;
    case BoolOpKind::IMPL:
      return Kind::IMPLIES;
    case BoolOpKind::IFF:
      return Kind::IFF;
    case BoolOpKind::ITE:
      return Kind::ITE;
    default:
      break;
    }
    break;
  case OpFamilyId::CompareOp:
    switch (llvm::cast<CompareOp>(e->op()).m_kind) {
    case CompareOpKind::EQ:
      return Kind::EQUAL;
    case CompareOpKind::NEQ:
      return Kind::DISTINCT;
    default:
      break;
    }
    break;
  case OpFamilyId::BvOp:
    switch (llvm::cast<BvOp>(e->op()).m_kind) {
    case BvOpKind::BNOT:
      return Kind::BV_NOT;
    // -- the result is 1 bit wide, as in Z3 (SeaHorn's type checker says
    // -- the argument's width, but only Z3 terms converted back build these)
    case BvOpKind::BREDAND:
      return Kind::BV_REDAND;
    case BvOpKind::BREDOR:
      return Kind::BV_REDOR;
    case BvOpKind::BAND:
      return Kind::BV_AND;
    case BvOpKind::BOR:
      return Kind::BV_OR;
    case BvOpKind::BXOR:
      return Kind::BV_XOR;
    case BvOpKind::BNAND:
      return Kind::BV_NAND;
    case BvOpKind::BNOR:
      return Kind::BV_NOR;
    case BvOpKind::BXNOR:
      return Kind::BV_XNOR;
    case BvOpKind::BADD:
      return Kind::BV_ADD;
    case BvOpKind::BSUB:
      return Kind::BV_SUB;
    case BvOpKind::BNEG:
      return Kind::BV_NEG;
    case BvOpKind::BMUL:
      return Kind::BV_MUL;
    // -- division and remainder by zero follow SMT-LIB in Bitwuzla and Z3
    case BvOpKind::BUDIV:
      return Kind::BV_UDIV;
    case BvOpKind::BSDIV:
      return Kind::BV_SDIV;
    case BvOpKind::BUREM:
      return Kind::BV_UREM;
    case BvOpKind::BSREM:
      return Kind::BV_SREM;
    case BvOpKind::BSMOD:
      return Kind::BV_SMOD;
    case BvOpKind::BSHL:
      return Kind::BV_SHL;
    case BvOpKind::BLSHR:
      return Kind::BV_SHR;
    case BvOpKind::BASHR:
      return Kind::BV_ASHR;
    case BvOpKind::BULT:
      return Kind::BV_ULT;
    case BvOpKind::BSLT:
      return Kind::BV_SLT;
    case BvOpKind::BULE:
      return Kind::BV_ULE;
    case BvOpKind::BSLE:
      return Kind::BV_SLE;
    case BvOpKind::BUGE:
      return Kind::BV_UGE;
    case BvOpKind::BSGE:
      return Kind::BV_SGE;
    case BvOpKind::BUGT:
      return Kind::BV_UGT;
    case BvOpKind::BSGT:
      return Kind::BV_SGT;
    case BvOpKind::BEXTRACT:
      return Kind::BV_EXTRACT;
    case BvOpKind::BSEXT:
      return Kind::BV_SIGN_EXTEND;
    case BvOpKind::BZEXT:
      return Kind::BV_ZERO_EXTEND;
    case BvOpKind::BCONCAT:
      return Kind::BV_CONCAT;
    case BvOpKind::BREPEAT:
      return Kind::BV_REPEAT;
    case BvOpKind::BROTATE_LEFT:
      return Kind::BV_ROLI;
    case BvOpKind::BROTATE_RIGHT:
      return Kind::BV_RORI;
    // -- the overflow test; mkNoOverflow adds the direction
    case BvOpKind::UADD_NO_OVERFLOW:
      return Kind::BV_UADD_OVERFLOW;
    case BvOpKind::USUB_NO_UNDERFLOW:
      return Kind::BV_USUB_OVERFLOW;
    case BvOpKind::UMUL_NO_OVERFLOW:
      return Kind::BV_UMUL_OVERFLOW;
    case BvOpKind::SADD_NO_OVERFLOW:
    case BvOpKind::SADD_NO_UNDERFLOW:
      return Kind::BV_SADD_OVERFLOW;
    case BvOpKind::SSUB_NO_OVERFLOW:
    case BvOpKind::SSUB_NO_UNDERFLOW:
      return Kind::BV_SSUB_OVERFLOW;
    case BvOpKind::SMUL_NO_OVERFLOW:
    case BvOpKind::SMUL_NO_UNDERFLOW:
      return Kind::BV_SMUL_OVERFLOW;
    case BvOpKind::INT2BV:
    case BvOpKind::BV2INT:
      throw UnsupportedExpr(e, "Bitwuzla has no integers");
    // -- nothing in SeaHorn builds these, and their type rule (an unsigned
    // -- amount) disagrees with Z3's ext_rotate (a bit-vector amount)
    case BvOpKind::BEXT_ROTATE_LEFT:
    case BvOpKind::BEXT_ROTATE_RIGHT:
      throw UnsupportedExpr(e, "rotation by a term is not supported by "
                               "Bitwuzla adapter");
    default:
      break;
    }
    break;
  case OpFamilyId::BindOp:
    if (isOpX<FAPP>(e)) {
      if (bind::isFdecl(bind::fname(e)))
        throw UnsupportedExpr(e, "uninterpreted functions are not supported "
                                 "by Bitwuzla adapter yet");
      // -- the application of a term: a lambda, or an array
      return Kind::APPLY;
    }
    break;
  case OpFamilyId::ArrayOp:
    switch (llvm::cast<ArrayOp>(e->op()).m_kind) {
    case ArrayOpKind::SELECT:
      return Kind::ARRAY_SELECT;
    case ArrayOpKind::STORE:
      return Kind::ARRAY_STORE;
    case ArrayOpKind::CONST_ARRAY:
      return Kind::CONST_ARRAY;
    default:
      // -- array-map, array-default, as-array
      break;
    }
    break;
  default:
    break;
  }
  throw UnsupportedExpr(e, "operator not supported by Bitwuzla adapter yet");
}

/// The children of \p e that are terms, as [first, last): (extract hi lo
/// bv), (sext bv sort), (repeat n bv), (rotate n bv) and (const-array sort
/// v) also have numerals and sorts as children
static std::pair<unsigned, unsigned> termArgs(Expr e) {
  if (isOpX<BEXTRACT>(e))
    return {2, 3};
  if (isOpX<BSEXT>(e) || isOpX<BZEXT>(e))
    return {0, 1};
  if (isOpX<BREPEAT>(e) || isOpX<BROTATE_LEFT>(e) || isOpX<BROTATE_RIGHT>(e) ||
      isOpX<CONST_ARRAY>(e))
    return {1, 2};
  return {0, static_cast<unsigned>(e->arity())};
}

/// SeaHorn's overflow predicates, as Z3 defines them: true when the exact
/// result is in range. Z3 splits signed overflow by direction, while
/// Bitwuzla's signed tests \p k are true when the result is out of range in
/// either direction. An out-of-range signed sum or difference is too large
/// iff the first argument is non-negative, and a product iff the signs agree.
static Term mkNoOverflow(bitwuzla::TermManager &tm, Expr e, Kind k,
                         const std::vector<Term> &args) {
  Term out = tm.mk_term(k, args); // -- checks that there are two arguments
  auto neg = [&](const Term &t) {
    return tm.mk_term(Kind::BV_SLT, {t, tm.mk_bv_zero(t.sort())});
  };
  switch (llvm::cast<BvOp>(e->op()).m_kind) {
  case BvOpKind::SADD_NO_OVERFLOW:
  case BvOpKind::SSUB_NO_OVERFLOW:
    out = tm.mk_term(Kind::AND, {out, tm.mk_term(Kind::NOT, {neg(args[0])})});
    break;
  case BvOpKind::SADD_NO_UNDERFLOW:
  case BvOpKind::SSUB_NO_UNDERFLOW:
    out = tm.mk_term(Kind::AND, {out, neg(args[0])});
    break;
  case BvOpKind::SMUL_NO_OVERFLOW:
    out = tm.mk_term(Kind::AND, {out, tm.mk_term(Kind::EQUAL, {neg(args[0]),
                                                               neg(args[1])})});
    break;
  case BvOpKind::SMUL_NO_UNDERFLOW:
    out = tm.mk_term(
        Kind::AND,
        {out, tm.mk_term(Kind::DISTINCT, {neg(args[0]), neg(args[1])})});
    break;
  default:
    // -- unsigned: only one direction is possible
    break;
  }
  return tm.mk_term(Kind::NOT, {out});
}

Sort marshal_bitwuzla::encode_sort(Expr s) {
  if (isOpX<BOOL_TY>(s))
    return m_tm.mk_bool_sort();
  if (isOpX<BVSORT>(s)) {
    try {
      return m_tm.mk_bv_sort(bv::width(s));
    } catch (bitwuzla::Exception &ex) {
      throw UnsupportedExpr(s, "Bitwuzla rejects the sort: " + ex.msg());
    }
  }
  if (isOpX<ARRAY_TY>(s)) {
    // -- memory maps bit-vectors to bit-vectors; nothing else is needed yet
    if (!isOpX<BVSORT>(sort::arrayIndexTy(s)) ||
        !isOpX<BVSORT>(sort::arrayValTy(s)))
      throw UnsupportedExpr(s, "only arrays from bit-vectors to bit-vectors "
                               "are supported by Bitwuzla adapter");
    return m_tm.mk_array_sort(encode_sort(sort::arrayIndexTy(s)),
                              encode_sort(sort::arrayValTy(s)));
  }
  if (isOpX<INT_TY>(s) || isOpX<REAL_TY>(s))
    throw UnsupportedExpr(s, "Bitwuzla has no integer or real sort");
  throw UnsupportedExpr(s, "sort not supported by Bitwuzla adapter yet");
}

Term marshal_bitwuzla::declare(Expr fdecl) {
  if (bind::domainSz(fdecl) > 0)
    throw UnsupportedExpr(fdecl, "uninterpreted functions are not supported "
                                 "by Bitwuzla adapter yet");
  // -- identity comes from the cache: two declarations may print the same
  return m_tm.mk_const(encode_sort(bind::rangeTy(fdecl)), get_name(fdecl));
}

marshal_bitwuzla::Encoded marshal_bitwuzla::mkBoundVar(Expr e) {
  // -- de Bruijn index as in Z3: 0 is the last variable of the innermost
  // -- binder, then the others of that binder, then the enclosing binder's
  unsigned rest = bind::bvarId(e);
  for (auto it = m_scopes.rbegin(), end = m_scopes.rend(); it != end; ++it) {
    unsigned k = it->vars.size();
    if (rest < k) {
      Term v = it->vars[k - 1 - rest];
      Sort declared;
      try {
        declared = encode_sort(bind::type(e));
      } catch (UnsupportedExpr &ex) {
        throw UnsupportedExpr(e, ex.what());
      }
      if (v.sort() != declared)
        throw UnsupportedExpr(e, "bound variable of another sort than its "
                                 "binder's");
      return {v, bind::bvarId(e) + 1};
    }
    rest -= k;
  }
  throw UnsupportedExpr(e, "bound variable outside of its binder");
}

marshal_bitwuzla::Encoded marshal_bitwuzla::mkLeaf(Expr e) {
  if (isOpX<TRUE>(e))
    return {m_tm.mk_true(), 0};
  if (isOpX<FALSE>(e))
    return {m_tm.mk_false(), 0};
  if (bind::isBVar(e))
    return mkBoundVar(e);

  try {
    if (bv::is_bvnum(e)) {
      Sort sort = encode_sort(e->arg(1));
      const expr::mpz_class &num = getTerm<expr::mpz_class>(e->arg(0));
      // -- the decimal string keeps values wider than 64 bits. Bitwuzla
      // -- rejects values outside of [0, 2^width), so reduce modulo 2^width.
      mpz_t r;
      mpz_init(r);
      mpz_fdiv_r_2exp(r, num.get_mpz_t(), sort.bv_size());
      std::string snum = expr::mpz_class(r).to_string();
      mpz_clear(r);
      return {m_tm.mk_bv_value(sort, snum, 10), 0};
    }
    if (bind::isFapp(e) && bind::isFdecl(bind::fname(e)))
      return {declare(bind::fname(e)), 0};
  } catch (UnsupportedExpr &ex) {
    // -- report the numeral or constant rather than its sort
    throw UnsupportedExpr(e, ex.what());
  } catch (bitwuzla::Exception &ex) {
    throw UnsupportedExpr(e, "Bitwuzla rejects the encoding: " + ex.msg());
  }

  throw UnsupportedExpr(e, "term not supported by Bitwuzla adapter yet");
}

Term marshal_bitwuzla::mkNode(Expr e, const std::vector<Term> &args) {
  Kind k = kindOf(e);
  try {
    switch (k) {
    case Kind::APPLY:
      return mkApp(e, args.at(0),
                   std::vector<Term>(args.begin() + 1, args.end()));
    case Kind::ARRAY_SELECT:
      if (args.at(0).sort().is_fun())
        return mkApp(e, args[0],
                     std::vector<Term>(args.begin() + 1, args.end()));
      return m_tm.mk_term(k, args);
    case Kind::ARRAY_STORE:
      if (args.size() != 3)
        throw UnsupportedExpr(e, "expected three arguments");
      return mkStore(e, args[0], args[1], args[2]);
    case Kind::ITE:
      if (args.size() != 3)
        throw UnsupportedExpr(e, "expected three arguments");
      return mkIte(e, args[0], args[1], args[2]);
    case Kind::BV_EXTRACT:
      return m_tm.mk_term(k, args, {bv::high(e), bv::low(e)});
    case Kind::BV_SIGN_EXTEND:
    case Kind::BV_ZERO_EXTEND: {
      // -- SeaHorn stores the target sort, Bitwuzla wants the extension amount
      uint64_t in_width = args.at(0).sort().bv_size();
      uint64_t out_width = bv::width(e->arg(1));
      if (out_width < in_width)
        throw UnsupportedExpr(e, "extension to a narrower sort");
      if (out_width == in_width)
        return args[0];
      return m_tm.mk_term(k, args, {out_width - in_width});
    }
    case Kind::BV_REPEAT:
    case Kind::BV_ROLI:
    case Kind::BV_RORI:
      if (!isOpX<UINT>(e->arg(0)))
        throw UnsupportedExpr(e, "expected an unsigned numeral as index");
      return m_tm.mk_term(k, args, {getTerm<unsigned>(e->arg(0))});
    case Kind::IMPLIES:
    case Kind::IFF:
    case Kind::EQUAL:
    case Kind::DISTINCT:
      // -- binary in SeaHorn's type rules. Bitwuzla would chain more
      // -- arguments, and SeaHorn's evaluator and Z3's encoder would each
      // -- read them differently, so there is no agreed meaning to encode.
      if (args.size() != 2)
        throw UnsupportedExpr(e, "expected two arguments");
      if (k == Kind::EQUAL || k == Kind::DISTINCT)
        return mkEq(e, k, args[0], args[1]);
      return m_tm.mk_term(k, args);
    case Kind::BV_UADD_OVERFLOW:
    case Kind::BV_USUB_OVERFLOW:
    case Kind::BV_UMUL_OVERFLOW:
    case Kind::BV_SADD_OVERFLOW:
    case Kind::BV_SSUB_OVERFLOW:
    case Kind::BV_SMUL_OVERFLOW:
      return mkNoOverflow(m_tm, e, k, args);
    case Kind::CONST_ARRAY: {
      // -- SeaHorn gives the index sort, Bitwuzla wants the array sort
      if (!isOpX<BVSORT>(e->arg(0)) || !args.at(0).sort().is_bv())
        throw UnsupportedExpr(e, "only arrays from bit-vectors to bit-vectors "
                                 "are supported by Bitwuzla adapter");
      Sort index = encode_sort(e->arg(0));
      return m_tm.mk_const_array(m_tm.mk_array_sort(index, args[0].sort()),
                                 args[0]);
    }
    case Kind::AND:
    case Kind::OR:
    case Kind::XOR:
    case Kind::BV_AND:
    case Kind::BV_OR:
    case Kind::BV_XOR:
    case Kind::BV_ADD:
    case Kind::BV_MUL:
    case Kind::BV_CONCAT:
      // -- n-ary in both, but Bitwuzla wants at least two arguments
      if (args.size() == 1)
        return args[0];
      return m_tm.mk_term(k, args);
    default:
      return m_tm.mk_term(k, args);
    }
  } catch (bitwuzla::Exception &ex) {
    throw UnsupportedExpr(e, "Bitwuzla rejects the encoding: " + ex.msg());
  }
}

bool marshal_bitwuzla::lookup(Expr e, Encoded &out) const {
  auto it = m_cache.find(e);
  if (it != m_cache.end()) {
    out = {it->second, 0};
    return true;
  }
  // -- a term with a free bound variable is only valid under the binder it
  // -- was built under, the innermost one
  if (!m_scopes.empty()) {
    auto jt = m_scopes.back().cache.find(e);
    if (jt != m_scopes.back().cache.end()) {
      out = jt->second;
      return true;
    }
  }
  return false;
}

void marshal_bitwuzla::remember(Expr e, const Encoded &enc) {
  if (enc.fv == 0)
    m_cache.insert({e, enc.term});
  else if (!m_scopes.empty())
    m_scopes.back().cache.insert({e, enc});
  else
    throw UnsupportedExpr(e, "term with a free bound variable");
}

Term marshal_bitwuzla::freshVar(const Sort &s, const std::string &name) {
  // -- distinct names, so that the term prints unambiguously
  return m_tm.mk_var(s, name + "!" + std::to_string(++m_num_vars));
}

std::vector<Term> marshal_bitwuzla::freshVars(const Sort &fun) {
  std::vector<Term> vars;
  for (const Sort &s : fun.fun_domain())
    vars.push_back(freshVar(s, "x"));
  return vars;
}

void marshal_bitwuzla::enterBinder(Expr e) {
  Scope scope;
  for (unsigned i = 0, sz = bind::numBound(e); i < sz; ++i) {
    Sort s;
    try {
      s = encode_sort(bind::boundSort(e, i));
    } catch (UnsupportedExpr &ex) {
      throw UnsupportedExpr(e, ex.what());
    }
    if (!s.is_bv() && !s.is_bool())
      throw UnsupportedExpr(e, "only bit-vector and Bool variables are "
                               "supported in binders by Bitwuzla adapter");
    scope.vars.push_back(freshVar(s, get_name(bind::decl(e, i))));
  }
  m_scopes.push_back(std::move(scope));
}

marshal_bitwuzla::Encoded marshal_bitwuzla::leaveBinder(Expr e) {
  Encoded body;
  bool found = lookup(bind::body(e), body);
  assert(found && "the body of a binder is not encoded");
  (void)found;
  std::vector<Term> args = m_scopes.back().vars;
  unsigned bound = args.size();
  m_scopes.pop_back();

  // -- Bitwuzla merges (lambda x (lambda y b)) into one function of x and y,
  // -- which SeaHorn would apply differently
  if (isOpX<LAMBDA>(e) && body.term.sort().is_fun())
    throw UnsupportedExpr(e, "lambda whose body is a function");
  args.push_back(body.term);
  Kind k = isOpX<LAMBDA>(e)   ? Kind::LAMBDA
           : isOpX<FORALL>(e) ? Kind::FORALL
                              : Kind::EXISTS;
  Term res;
  try {
    res = m_tm.mk_term(k, args);
  } catch (bitwuzla::Exception &ex) {
    throw UnsupportedExpr(e, "Bitwuzla rejects the encoding: " + ex.msg());
  }
  return {res, body.fv > bound ? body.fv - bound : 0};
}

Term marshal_bitwuzla::mkApp(Expr e, const Term &f,
                             const std::vector<Term> &args) {
  if (f.sort().is_fun()) {
    std::vector<Term> v{f};
    v.insert(v.end(), args.begin(), args.end());
    return m_tm.mk_term(Kind::APPLY, v);
  }
  if (f.sort().is_array() && args.size() == 1)
    return m_tm.mk_term(Kind::ARRAY_SELECT, {f, args[0]});
  throw UnsupportedExpr(e, "application of a term that is neither a "
                           "function nor an array of one index");
}

Term marshal_bitwuzla::mkEq(Expr e, Kind k, const Term &a, const Term &b) {
  if (!a.sort().is_fun() && !b.sort().is_fun())
    return m_tm.mk_term(k, {a, b});
  // -- pointwise: Bitwuzla has no equality between functions
  std::vector<Term> vars = freshVars((a.sort().is_fun() ? a : b).sort());
  Term body = m_tm.mk_term(Kind::EQUAL, {mkApp(e, a, vars), mkApp(e, b, vars)});
  vars.push_back(body);
  Term all = m_tm.mk_term(Kind::FORALL, vars);
  return k == Kind::DISTINCT ? m_tm.mk_term(Kind::NOT, {all}) : all;
}

Term marshal_bitwuzla::mkIte(Expr e, const Term &c, const Term &t,
                             const Term &f) {
  if (!t.sort().is_fun() && !f.sort().is_fun())
    return m_tm.mk_term(Kind::ITE, {c, t, f});
  // -- inside a lambda: Bitwuzla 0.9.1 aborts on an ite between lambdas
  std::vector<Term> vars = freshVars((t.sort().is_fun() ? t : f).sort());
  Term body =
      m_tm.mk_term(Kind::ITE, {c, mkApp(e, t, vars), mkApp(e, f, vars)});
  vars.push_back(body);
  return m_tm.mk_term(Kind::LAMBDA, vars);
}

Term marshal_bitwuzla::mkStore(Expr e, const Term &a, const Term &i,
                               const Term &v) {
  if (!a.sort().is_fun())
    return m_tm.mk_term(Kind::ARRAY_STORE, {a, i, v});
  if (a.sort().fun_domain().size() != 1)
    throw UnsupportedExpr(e, "store into a function of more than one argument");
  Term x = freshVar(a.sort().fun_domain()[0], "x");
  Term body = m_tm.mk_term(
      Kind::ITE, {m_tm.mk_term(Kind::EQUAL, {x, i}), v, mkApp(e, a, {x})});
  return m_tm.mk_term(Kind::LAMBDA, {x, body});
}

Term marshal_bitwuzla::encode_term(Expr root) {
  // -- an explicit stack: the formulas of long paths can be very deep. The
  // -- flag is set once the children are pushed (or, for a binder, its body).
  std::vector<std::pair<Expr, bool>> todo{{root, false}};
  std::vector<Term> args;
  try {
    while (!todo.empty()) {
      Expr e = todo.back().first;
      Encoded enc;
      if (!todo.back().second) {
        if (lookup(e, enc)) {
          todo.pop_back();
          continue;
        }
        if (isBinder(e)) {
          todo.back().second = true;
          enterBinder(e);
          todo.push_back({bind::body(e), false});
          continue;
        }
        if (isLeaf(e)) {
          remember(e, mkLeaf(e));
          todo.pop_back();
          continue;
        }
        // -- reject an unsupported operator before encoding its arguments,
        // -- so that the error names the operator
        kindOf(e);
        todo.back().second = true;
        auto range = termArgs(e);
        for (unsigned i = range.first; i < range.second; ++i)
          if (!lookup(e->arg(i), enc))
            todo.push_back({e->arg(i), false});
        continue;
      }

      todo.pop_back();
      if (isBinder(e)) {
        // -- its body is encoded, and its scope is the innermost
        remember(e, leaveBinder(e));
        continue;
      }
      // -- all term arguments are encoded
      auto range = termArgs(e);
      args.clear();
      unsigned fv = 0;
      for (unsigned i = range.first; i < range.second; ++i) {
        bool found = lookup(e->arg(i), enc);
        assert(found && "an argument is not encoded");
        (void)found;
        args.push_back(enc.term);
        fv = std::max(fv, enc.fv);
      }
      remember(e, {mkNode(e, args), fv});
    }
  } catch (...) {
    // -- leave the encoder usable
    m_scopes.clear();
    throw;
  }
  Encoded res;
  bool found = lookup(root, res);
  assert(found && res.fv == 0);
  (void)found;
  return res.term;
}

/// An array value: a chain of stores of values over a constant array of a
/// value, as get_value gives it. Rebuilt in the same order, so it is the
/// same function even if an index were stored twice.
static Expr decodeArray(const Term &v, ExprFactory &efac) {
  std::vector<Term> stores;
  Term base = v;
  while (base.kind() == Kind::ARRAY_STORE) {
    stores.push_back(base);
    base = base[0];
  }
  Sort index = v.sort().array_index();
  if (base.kind() != Kind::CONST_ARRAY || !index.is_bv())
    return Expr();
  Expr dflt = decode_bitwuzla_value(base[0], efac);
  if (!dflt)
    return Expr();
  Expr res = op::array::constArray(bv::bvsort(index.bv_size(), efac), dflt);
  for (auto it = stores.rbegin(); it != stores.rend(); ++it) {
    Expr i = decode_bitwuzla_value((*it)[1], efac);
    Expr x = decode_bitwuzla_value((*it)[2], efac);
    if (!i || !x)
      return Expr();
    res = op::array::store(res, i, x);
  }
  return res;
}

Expr decode_bitwuzla_value(const Term &v, ExprFactory &efac) {
  if (v.sort().is_array())
    return decodeArray(v, efac);
  if (!v.is_value())
    return Expr();
  Sort s = v.sort();
  if (s.is_bool())
    return v.value<bool>() ? mk<TRUE>(efac) : mk<FALSE>(efac);
  if (s.is_bv())
    // -- base 10 gives the unsigned number of the bits
    return bv::bvnum(expr::mpz_class(v.value<std::string>(10)), s.bv_size(),
                     efac);
  return Expr();
}

} // namespace solver
} // namespace seahorn

#endif
