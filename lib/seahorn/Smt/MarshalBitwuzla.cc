#ifdef WITH_BITWUZLA

#include "seahorn/Expr/Smt/MarshalBitwuzla.hh"
#include "seahorn/Expr/ExprLlvm.hh"

#include "llvm/Support/Casting.h"
#include "llvm/Support/raw_ostream.h"

#include "boost/lexical_cast.hpp"

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

/// Exprs that are encoded without encoding any children first: Boolean
/// values, numerals (BIND) and constants (FAPP of a declaration alone)
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
  default:
    break;
  }
  throw UnsupportedExpr(e, "operator not supported by Bitwuzla adapter yet");
}

/// The children of \p e that are terms, as [first, last): (extract hi lo
/// bv), (sext bv sort), (repeat n bv) and (rotate n bv) also have numerals
/// and sorts as children
static std::pair<unsigned, unsigned> termArgs(Expr e) {
  if (isOpX<BEXTRACT>(e))
    return {2, 3};
  if (isOpX<BSEXT>(e) || isOpX<BZEXT>(e))
    return {0, 1};
  if (isOpX<BREPEAT>(e) || isOpX<BROTATE_LEFT>(e) || isOpX<BROTATE_RIGHT>(e))
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

Term marshal_bitwuzla::mkLeaf(Expr e) {
  if (isOpX<TRUE>(e))
    return m_tm.mk_true();
  if (isOpX<FALSE>(e))
    return m_tm.mk_false();

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
      return m_tm.mk_bv_value(sort, snum, 10);
    }
    if (bind::isFapp(e) && bind::isFdecl(bind::fname(e)))
      return declare(bind::fname(e));
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
      return m_tm.mk_term(k, args);
    case Kind::BV_UADD_OVERFLOW:
    case Kind::BV_USUB_OVERFLOW:
    case Kind::BV_UMUL_OVERFLOW:
    case Kind::BV_SADD_OVERFLOW:
    case Kind::BV_SSUB_OVERFLOW:
    case Kind::BV_SMUL_OVERFLOW:
      return mkNoOverflow(m_tm, e, k, args);
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

Term marshal_bitwuzla::encode_term(Expr root) {
  // -- an explicit stack: the formulas of long paths can be very deep
  std::vector<std::pair<Expr, bool>> todo{{root, false}};
  std::vector<Term> args;

  while (!todo.empty()) {
    Expr e = todo.back().first;
    if (m_cache.count(e)) {
      todo.pop_back();
      continue;
    }
    if (isLeaf(e)) {
      m_cache.insert({e, mkLeaf(e)});
      todo.pop_back();
      continue;
    }

    auto range = termArgs(e);
    if (!todo.back().second) {
      // -- reject an unsupported operator before encoding its arguments, so
      // -- that the error names the operator
      kindOf(e);
      todo.back().second = true;
      for (unsigned i = range.first; i < range.second; ++i)
        if (!m_cache.count(e->arg(i)))
          todo.push_back({e->arg(i), false});
      continue;
    }

    // -- all term arguments are encoded
    args.clear();
    for (unsigned i = range.first; i < range.second; ++i)
      args.push_back(m_cache.at(e->arg(i)));
    m_cache.insert({e, mkNode(e, args)});
    todo.pop_back();
  }
  return m_cache.at(root);
}

} // namespace solver
} // namespace seahorn

#endif
