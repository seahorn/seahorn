#ifdef WITH_BITWUZLA
/* Unit tests for the Bitwuzla encoder (marshal_bitwuzla) and solver */
#define DOCTEST_CONFIG_IMPLEMENT_WITH_MAIN

#include "seahorn/Expr/Expr.hh"
#include "seahorn/Expr/ExprLlvm.hh"
#include "seahorn/Expr/ExprOpBinder.hh"
#include "seahorn/Expr/ExprVisitor.hh"
#include "seahorn/Expr/Smt/BitwuzlaEncodingCheck.hh"
#include "seahorn/Expr/Smt/BitwuzlaSolverImpl.hh"
#include "seahorn/Expr/Smt/EZ3.hh"
#include "seahorn/Expr/Smt/MarshalBitwuzla.hh"

#include "boost/lexical_cast.hpp"
#include "llvm/Support/CommandLine.h"

#include <csignal>
#include <cstdio>
#include <dirent.h>
#include <cstdlib>
#include <fstream>
#include <poll.h>
#include <sys/wait.h>
#include <unistd.h>
#include <functional>
#include <iterator>
#include <map>
#include <random>
#include <string>

#include "sea_doctest.hh" // doctest is last to avoid name clash
// -- with DOCTEST_CONFIG_IMPLEMENT, doctest includes macOS's <mach/boolean.h>,
// -- which defines TRUE and FALSE as macros
#undef TRUE
#undef FALSE

using namespace expr;
using namespace seahorn;
using seahorn::solver::bitwuzla_solver_impl;
using seahorn::solver::checkBitwuzlaEncoding;
using seahorn::solver::checkSmtLibTermWithZ3;
using seahorn::solver::decode_bitwuzla_value;
using seahorn::solver::EncodingVerdict;
using seahorn::solver::marshal_bitwuzla;
using seahorn::solver::Solver;
using seahorn::solver::SolverResult;
using seahorn::solver::UnsupportedExpr;
using seahorn::solver::verdictName;
namespace bz = bitwuzla;

namespace doctest {
template <> struct StringMaker<EncodingVerdict> {
  static String convert(EncodingVerdict v) { return verdictName(v); }
};
} // namespace doctest

namespace {
struct Env {
  ExprFactory efac;
  bz::TermManager tm;
  marshal_bitwuzla m{tm};

  Expr bvc(const std::string &name, unsigned w) {
    return bv::bvConst(mkTerm<std::string>(name, efac), w);
  }
  Expr boolc(const std::string &name) {
    return bind::boolConst(mkTerm<std::string>(name, efac));
  }
  Expr num(long v, unsigned w) {
    return bv::bvnum(expr::mpz_class(v), w, efac);
  }
  Expr bvsort(unsigned w) { return bv::bvsort(w, efac); }
  /// an array constant (uninterpreted) from bit-vectors of width \p iw to
  /// bit-vectors of width \p vw
  Expr arrc(const std::string &name, unsigned iw, unsigned vw) {
    return bind::mkConst(mkTerm<std::string>(name, efac),
                         sort::arrayTy(bvsort(iw), bvsort(vw)));
  }
  /// the bound variable of de Bruijn index \p i, a bit-vector of width \p w
  Expr bvar(unsigned i, unsigned w) { return bind::bvar(i, bvsort(w)); }
  /// a declaration of a bound variable of width \p w, for a binder
  Expr bdecl(const std::string &name, unsigned w) {
    return bind::fname(bind::mkConst(mkTerm<std::string>(name, efac), bvsort(w)));
  }
  /// (lambda (name : bv(w)) body), where body refers to it as bvar(0, w)
  Expr lam(const std::string &name, unsigned w, Expr body) {
    return mk<LAMBDA>(bdecl(name, w), body);
  }

  bz::Result check(Expr e) {
    bz::Bitwuzla s(tm);
    s.assert_formula(m.encode_term(e));
    return s.check_sat();
  }
  bool valid(Expr e) { return check(mk<NEG>(e)) == bz::Result::UNSAT; }

  /// \p e cannot be encoded, and the error names \p culprit
  bool rejects(Expr e, Expr culprit) {
    try {
      m.encode_term(e);
    } catch (UnsupportedExpr &ex) {
      return ex.expr() == culprit;
    }
    return false;
  }
};

using BinOp = std::function<Expr(Expr, Expr)>;
template <typename Op> BinOp binop() {
  return [](Expr a, Expr b) { return mk<Op>(a, b); };
}

/// Z3's value of a variable-free \p t (through the existing EZ3 path)
Expr z3Value(EZ3 &z3, Expr t, Expr r) {
  ZSolver<EZ3> solver(z3);
  solver.assertExpr(mk<EQ>(r, t));
  REQUIRE(bool(solver.solve()));
  return solver.getModel().eval(r);
}

/// \p v is a bit-vector numeral whose number is in [0, 2^w)
bool isUnsignedBvNum(Expr v) {
  unsigned w;
  if (!bv::isBvNum(v, w))
    return false;
  expr::mpz_class n = bv::toMpz(v);
  return n >= 0l && n < (expr::mpz_class(1ul) << w);
}

/// \p a and \p b are the same Bool value, or numerals of the same width with
/// the same bits (Z3's decoder may give a negative number for them)
bool sameValue(Expr a, Expr b) {
  if (isOpX<TRUE>(a) || isOpX<FALSE>(a))
    return a == b;
  unsigned wa, wb;
  if (!bv::isBvNum(a, wa) || !bv::isBvNum(b, wb) || wa != wb)
    return false;
  expr::mpz_class mod = expr::mpz_class(1ul) << wa;
  return bv::toMpz(a) % mod == bv::toMpz(b) % mod;
}

/// Appends to \p out the terms of \p e not in \p seen, in a fixed order: \p e
/// and, below it, every argument that is a term (not the indices of extract,
/// nor the sort of an extension)
void termsOf(Expr e, ExprSet &seen, ExprVector &out) {
  if (!seen.insert(e).second)
    return;
  out.push_back(e);
  // -- the body of a binder is not a closed term (plan 1.7)
  if (bind::IsConst()(e) || bv::is_bvnum(e) || isOpX<LAMBDA>(e) ||
      isOpX<FORALL>(e) || isOpX<EXISTS>(e))
    return;
  if (isOpX<BEXTRACT>(e)) {
    termsOf(e->arg(2), seen, out);
    return;
  }
  if (isOpX<BSEXT>(e) || isOpX<BZEXT>(e)) {
    termsOf(e->arg(0), seen, out);
    return;
  }
  if (isOpX<CONST_ARRAY>(e)) {
    termsOf(e->arg(1), seen, out);
    return;
  }
  for (unsigned i = 0, sz = e->arity(); i < sz; ++i)
    termsOf(e->arg(i), seen, out);
}

/// \p e is a function, built as the fuzzer builds them: a lambda, an ite
/// of functions, or a store into a function
bool isFunctionTerm(Expr e) {
  if (isOpX<LAMBDA>(e))
    return true;
  if (isOpX<ITE>(e))
    return isFunctionTerm(e->arg(1)) || isFunctionTerm(e->arg(2));
  if (isOpX<STORE>(e))
    return isFunctionTerm(e->arg(0));
  return false;
}

/// \p e is a term of array sort, built as the fuzzer builds them: an array
/// constant, const-array, store, or ite of arrays
bool isArrayTerm(Expr e) {
  if (isOpX<STORE>(e))
    return isArrayTerm(e->arg(0));
  if (isOpX<CONST_ARRAY>(e))
    return true;
  if (isOpX<ITE>(e))
    return isArrayTerm(e->arg(1)) && isArrayTerm(e->arg(2));
  return bind::IsConst()(e) && isOpX<ARRAY_TY>(bind::rangeTy(bind::fname(e)));
}

/// Some subterm of \p e satisfies \p pred
bool anySubterm(Expr e, const std::function<bool(Expr)> &pred) {
  ExprSet seen;
  ExprVector todo{e};
  while (!todo.empty()) {
    Expr x = todo.back();
    todo.pop_back();
    if (!seen.insert(x).second)
      continue;
    if (pred(x))
      return true;
    todo.insert(todo.end(), x->args_begin(), x->args_end());
  }
  return false;
}

/// Bitwuzla gets a quantifier for \p e: it has a forall or an exists, or
/// an equality or disequality with a function (stated pointwise)
bool needsQuantifier(Expr e) {
  return anySubterm(e, [](Expr x) {
    return isOpX<FORALL>(x) || isOpX<EXISTS>(x) ||
           ((isOpX<EQ>(x) || isOpX<NEQ>(x)) &&
            (isFunctionTerm(x->arg(0)) || isFunctionTerm(x->arg(1))));
  });
}

/// \p e has an equality or disequality between arrays inside
bool hasArrayEquality(Expr e) {
  return anySubterm(e, [](Expr x) {
    return (isOpX<EQ>(x) || isOpX<NEQ>(x)) && isArrayTerm(x->arg(0));
  });
}

/// The index width of an array term built as the fuzzer builds them
unsigned indexWidthOf(Expr a) {
  if (isOpX<STORE>(a))
    return indexWidthOf(a->arg(0));
  if (isOpX<ITE>(a))
    return indexWidthOf(a->arg(1));
  if (isOpX<CONST_ARRAY>(a))
    return bv::width(a->arg(0));
  return bv::width(sort::arrayIndexTy(bind::rangeTy(bind::fname(a))));
}

/// \p e has an equality or disequality between arrays with indices narrower
/// than 32 bits inside
bool hasNarrowArrayEquality(Expr e) {
  return anySubterm(e, [](Expr x) {
    return (isOpX<EQ>(x) || isOpX<NEQ>(x)) && isArrayTerm(x->arg(0)) &&
           indexWidthOf(x->arg(0)) < 32;
  });
}

/// \p v is an array value: a store chain of unsigned numerals over a
/// const-array of an unsigned numeral
bool isArrayValue(Expr v) {
  while (isOpX<STORE>(v)) {
    if (!isUnsignedBvNum(v->arg(1)) || !isUnsignedBvNum(v->arg(2)))
      return false;
    v = v->arg(0);
  }
  return isOpX<CONST_ARRAY>(v) && isOpX<BVSORT>(v->arg(0)) &&
         isUnsignedBvNum(v->arg(1));
}
} // namespace

TEST_CASE("bitwuzla.sorts") {
  Env env;
  CHECK(env.m.encode_sort(sort::boolTy(env.efac)).is_bool());
  CHECK(env.m.encode_sort(env.bvsort(13)).bv_size() == 13);
  CHECK_THROWS_AS(env.m.encode_sort(sort::intTy(env.efac)), UnsupportedExpr);
  CHECK_THROWS_AS(env.m.encode_sort(sort::realTy(env.efac)), UnsupportedExpr);
  // -- arrays from bit-vectors to bit-vectors (plan 1.6), and no others
  bz::Sort arr = env.m.encode_sort(sort::arrayTy(env.bvsort(64), env.bvsort(8)));
  REQUIRE(arr.is_array());
  CHECK(arr.array_index().bv_size() == 64);
  CHECK(arr.array_element().bv_size() == 8);
  Expr boolTy = sort::boolTy(env.efac), intTy = sort::intTy(env.efac);
  for (Expr bad : {sort::arrayTy(boolTy, env.bvsort(8)),
                   sort::arrayTy(env.bvsort(8), boolTy),
                   sort::arrayTy(intTy, env.bvsort(8)),
                   sort::arrayTy(env.bvsort(8), intTy),
                   sort::arrayTy(env.bvsort(8),
                                 sort::arrayTy(env.bvsort(8), env.bvsort(8)))}) {
    INFO(*bad);
    CHECK_THROWS_AS(env.m.encode_sort(bad), UnsupportedExpr);
  }
}

TEST_CASE("bitwuzla.constants") {
  Env env;
  Expr x = env.bvc("x", 8);
  bz::Term tx = env.m.encode_term(x);
  CHECK(tx.is_const());
  CHECK(tx.sort().bv_size() == 8);
  CHECK(tx.symbol().value().get() == "x");
  // -- the cache gives one Bitwuzla constant per SeaHorn constant
  CHECK(env.m.encode_term(x) == tx);
  CHECK(env.m.encode_term(mk<BADD>(x, x)) == env.m.encode_term(mk<BADD>(x, x)));
  // -- constants of different sorts with the same name stay different
  CHECK(env.m.encode_term(env.bvc("x", 16)) != tx);
  CHECK(env.m.encode_term(env.boolc("b")).sort().is_bool());
}

TEST_CASE("bitwuzla.numerals") {
  Env env;
  // -- wider than 64 bits: 2^100 - 1
  Expr n100 = bv::bvnum(expr::mpz_class("1267650600228229401496703205375"), 128,
                        env.efac);
  Expr two100 = bv::bvnum(expr::mpz_class("1267650600228229401496703205376"),
                          128, env.efac);
  CHECK(env.m.encode_term(n100).value<std::string>(10) ==
        "1267650600228229401496703205375");
  CHECK(env.valid(mk<EQ>(n100, mk<BADD>(two100, env.num(-1, 128)))));
  // -- negative and too-large values are taken modulo 2^width
  CHECK(env.m.encode_term(env.num(-1, 8)).value<std::string>(10) == "255");
  CHECK(env.m.encode_term(env.num(256 + 7, 8)).value<std::string>(10) == "7");
  CHECK(env.m.encode_term(env.num(-128, 8)).value<std::string>(10) == "128");
}

TEST_CASE("bitwuzla.boolean operators") {
  Env env;
  Expr p = env.boolc("p"), q = env.boolc("q");
  Expr t = mk<TRUE>(env.efac), f = mk<FALSE>(env.efac);
  CHECK(env.valid(mk<IMPL>(f, p)));
  CHECK(env.valid(
      mk<IFF>(mk<NEG>(mk<AND>(p, q)), mk<OR>(mk<NEG>(p), mk<NEG>(q)))));
  CHECK(env.valid(mk<IFF>(mk<XOR>(p, q), mk<NEQ>(p, q))));
  CHECK(env.valid(
      mk<EQ>(mk<ITE>(t, env.num(1, 4), env.num(2, 4)), env.num(1, 4))));
  CHECK(env.valid(mknary<OR>(ExprVector{p, q, mk<NEG>(p)})));
  CHECK(env.check(mknary<AND>(ExprVector{p, q, mk<NEG>(p)})) ==
        bz::Result::UNSAT);
  CHECK(env.check(t) == bz::Result::SAT);
  CHECK(env.check(f) == bz::Result::UNSAT);
}

TEST_CASE("bitwuzla.bit-vector operators") {
  Env env;
  Expr x = env.bvc("x", 8);
  Expr one = env.num(1, 8), min = env.num(0x80, 8), ab = env.num(0xAB, 8);
  CHECK(env.valid(mk<EQ>(mk<BSUB>(mk<BADD>(x, one), one), x)));
  CHECK(env.valid(mk<EQ>(mk<BADD>(x, mk<BNEG>(x)), env.num(0, 8))));
  // -- n-ary add
  CHECK(env.valid(mk<EQ>(mknary<BADD>(ExprVector{x, one, x}),
                         mk<BADD>(x, mk<BADD>(x, one)))));
  // -- 0x80 is the largest unsigned and the smallest signed of these
  CHECK(env.valid(mk<BULT>(one, min)));
  CHECK(env.valid(mk<BULE>(one, min)));
  CHECK(env.valid(mk<BUGT>(min, one)));
  CHECK(env.valid(mk<BUGE>(min, one)));
  CHECK(env.valid(mk<BSLT>(min, one)));
  CHECK(env.valid(mk<BSLE>(min, one)));
  CHECK(env.valid(mk<BSGT>(one, min)));
  CHECK(env.valid(mk<BSGE>(one, min)));
  CHECK(env.valid(mk<BULE>(x, x)));
  CHECK(env.check(mk<BULT>(x, x)) == bz::Result::UNSAT);

  CHECK(env.valid(mk<EQ>(bv::extract(7, 4, ab), env.num(0xA, 4))));
  CHECK(env.valid(mk<EQ>(bv::extract(3, 0, ab), env.num(0xB, 4))));
  CHECK(env.valid(mk<EQ>(bv::sext(env.num(0x8, 4), 8), env.num(0xF8, 8))));
  CHECK(env.valid(mk<EQ>(bv::zext(env.num(0x8, 4), 8), env.num(0x08, 8))));
  // -- extending to the same width is the identity
  CHECK(env.valid(mk<EQ>(bv::zext(x, 8), x)));
  // -- the first argument of concat is the most significant
  CHECK(env.valid(mk<EQ>(mk<BCONCAT>(env.num(0xA, 4), env.num(0xB, 4)), ab)));
  CHECK(
      env.valid(mk<EQ>(mk<BCONCAT>(env.num(1, 1), env.num(0, 1), env.num(1, 1)),
                       env.num(5, 3))));
}

TEST_CASE("bitwuzla.bit-vector operators agree with z3") {
  Env env;
  EZ3 z3(env.efac);
  const unsigned w = 3;

  // -- division and remainder by zero are included: both follow SMT-LIB
  // -- names are std::string: doctest prints a const char * as a pointer
  std::vector<std::pair<std::string, BinOp>> ops = {
      {"bvand", binop<BAND>()},
      {"bvor", binop<BOR>()},
      {"bvxor", binop<BXOR>()},
      {"bvnand", binop<BNAND>()},
      {"bvnor", binop<BNOR>()},
      {"bvxnor", binop<BXNOR>()},
      {"bvadd", binop<BADD>()},
      {"bvsub", binop<BSUB>()},
      {"bvmul", binop<BMUL>()},
      {"bvudiv", binop<BUDIV>()},
      {"bvsdiv", binop<BSDIV>()},
      {"bvurem", binop<BUREM>()},
      {"bvsrem", binop<BSREM>()},
      {"bvsmod", binop<BSMOD>()},
      {"bvshl", binop<BSHL>()},
      {"bvlshr", binop<BLSHR>()},
      {"bvashr", binop<BASHR>()},
      {"concat", binop<BCONCAT>()},
      {"bvult", binop<BULT>()},
      {"bvslt", binop<BSLT>()},
      {"bvule", binop<BULE>()},
      {"bvsle", binop<BSLE>()},
      {"bvuge", binop<BUGE>()},
      {"bvsge", binop<BSGE>()},
      {"bvugt", binop<BUGT>()},
      {"bvsgt", binop<BSGT>()},
      {"=", binop<EQ>()},
      {"distinct", binop<NEQ>()},
      // -- unary operators, applied to the first argument
      {"bvnot", [](Expr a, Expr) { return mk<BNOT>(a); }},
      {"bvneg", [](Expr a, Expr) { return mk<BNEG>(a); }},
      {"bvredand", [](Expr a, Expr) { return mk<BREDAND>(a); }},
      {"bvredor", [](Expr a, Expr) { return mk<BREDOR>(a); }},
      {"extract", [](Expr a, Expr) { return bv::extract(2, 1, a); }},
      {"sext", [](Expr a, Expr) { return bv::sext(a, 5); }},
      {"zext", [](Expr a, Expr) { return bv::zext(a, 5); }},
  };

  bz::Bitwuzla bzla(env.tm);
  unsigned checked = 0, disagreements = 0;
  for (auto &op : ops) {
    for (long a = 0; a < (1 << w); ++a) {
      for (long b = 0; b < (1 << w); ++b) {
        Expr t = op.second(env.num(a, w), env.num(b, w));
        // -- the sort of the result, as Bitwuzla sees it
        bz::Sort s = env.m.encode_term(t).sort();
        Expr r = s.is_bool() ? env.boolc("r") : env.bvc("r", s.bv_size());
        Expr expected = z3Value(z3, t, r);

        bzla.push(1);
        bzla.assert_formula(env.m.encode_term(mk<NEQ>(t, expected)));
        bool agrees = bzla.check_sat() == bz::Result::UNSAT;
        bzla.pop(1);
        ++checked;
        if (!agrees) {
          ++disagreements;
          MESSAGE(op.first << " " << a << " " << b << ": z3 says "
                           << boost::lexical_cast<std::string>(*expected));
        }
      }
    }
  }
  CHECK(checked == ops.size() * 64);
  CHECK(disagreements == 0);
}

TEST_CASE("bitwuzla.overflow predicates agree with z3 and with arithmetic") {
  Env env;
  EZ3 z3(env.efac);

  // -- expected truth value from exact integer arithmetic, given a and b as
  // -- signed and as unsigned values, and the width
  struct Pred {
    std::string name;
    BinOp mkop;
    std::function<bool(long, long, long, long, unsigned)> exact;
  };
  auto smin = [](unsigned w) { return -(1L << (w - 1)); };
  auto smax = [](unsigned w) { return (1L << (w - 1)) - 1; };
  auto umax = [](unsigned w) { return (1L << w) - 1; };
  std::vector<Pred> preds = {
      {"uadd_no_overflow", binop<UADD_NO_OVERFLOW>(),
       [&](long, long, long ua, long ub, unsigned w) {
         return ua + ub <= umax(w);
       }},
      {"usub_no_underflow", binop<USUB_NO_UNDERFLOW>(),
       [&](long, long, long ua, long ub, unsigned) { return ua - ub >= 0; }},
      {"umul_no_overflow", binop<UMUL_NO_OVERFLOW>(),
       [&](long, long, long ua, long ub, unsigned w) {
         return ua * ub <= umax(w);
       }},
      {"sadd_no_overflow", binop<SADD_NO_OVERFLOW>(),
       [&](long sa, long sb, long, long, unsigned w) {
         return sa + sb <= smax(w);
       }},
      {"sadd_no_underflow", binop<SADD_NO_UNDERFLOW>(),
       [&](long sa, long sb, long, long, unsigned w) {
         return sa + sb >= smin(w);
       }},
      {"ssub_no_overflow", binop<SSUB_NO_OVERFLOW>(),
       [&](long sa, long sb, long, long, unsigned w) {
         return sa - sb <= smax(w);
       }},
      {"ssub_no_underflow", binop<SSUB_NO_UNDERFLOW>(),
       [&](long sa, long sb, long, long, unsigned w) {
         return sa - sb >= smin(w);
       }},
      {"smul_no_overflow", binop<SMUL_NO_OVERFLOW>(),
       [&](long sa, long sb, long, long, unsigned w) {
         return sa * sb <= smax(w);
       }},
      {"smul_no_underflow", binop<SMUL_NO_UNDERFLOW>(),
       [&](long sa, long sb, long, long, unsigned w) {
         return sa * sb >= smin(w);
       }},
  };

  bz::Bitwuzla bzla(env.tm);
  unsigned checked = 0, z3_wrong = 0, bzla_wrong = 0;
  for (unsigned w = 1; w <= 4; ++w) {
    for (auto &p : preds) {
      for (long ua = 0; ua <= umax(w); ++ua) {
        for (long ub = 0; ub <= umax(w); ++ub) {
          long sa = ua > smax(w) ? ua - (1L << w) : ua;
          long sb = ub > smax(w) ? ub - (1L << w) : ub;
          bool expected = p.exact(sa, sb, ua, ub, w);
          Expr t = p.mkop(env.num(ua, w), env.num(ub, w));

          ZSolver<EZ3> solver(z3);
          solver.assertExpr(t);
          bool z3_says = bool(solver.solve());

          bzla.push(1);
          bzla.assert_formula(env.m.encode_term(t));
          bool bzla_says = bzla.check_sat() == bz::Result::SAT;
          bzla.pop(1);

          ++checked;
          if (z3_says != expected) {
            ++z3_wrong;
            MESSAGE("z3 " << p.name << " w=" << w << " " << sa << " " << sb);
          }
          if (bzla_says != expected) {
            ++bzla_wrong;
            MESSAGE("bitwuzla " << p.name << " w=" << w << " " << sa << " "
                                << sb);
          }
        }
      }
    }
  }
  // -- 9 predicates x (4 + 16 + 64 + 256) argument pairs
  CHECK(checked == 9 * 340);
  CHECK(z3_wrong == 0);
  CHECK(bzla_wrong == 0);
}

TEST_CASE("bitwuzla.boolean operators agree with z3") {
  Env env;
  EZ3 z3(env.efac);
  Expr b[2] = {mk<FALSE>(env.efac), mk<TRUE>(env.efac)};
  Expr five = env.num(5, 4), nine = env.num(9, 4);

  // -- every operator on every assignment of three truth values; operators
  // -- with fewer arguments ignore the last ones
  using TernOp = std::function<Expr(Expr, Expr, Expr)>;
  std::vector<std::pair<std::string, TernOp>> ops = {
      {"not", [](Expr a, Expr, Expr) { return mk<NEG>(a); }},
      {"and", [](Expr a, Expr b, Expr) { return mk<AND>(a, b); }},
      {"and3",
       [](Expr a, Expr b, Expr c) { return mknary<AND>(ExprVector{a, b, c}); }},
      {"or", [](Expr a, Expr b, Expr) { return mk<OR>(a, b); }},
      {"or3",
       [](Expr a, Expr b, Expr c) { return mknary<OR>(ExprVector{a, b, c}); }},
      {"xor", [](Expr a, Expr b, Expr) { return mk<XOR>(a, b); }},
      {"=>", [](Expr a, Expr b, Expr) { return mk<IMPL>(a, b); }},
      {"<=>", [](Expr a, Expr b, Expr) { return mk<IFF>(a, b); }},
      {"=", [](Expr a, Expr b, Expr) { return mk<EQ>(a, b); }},
      {"distinct", [](Expr a, Expr b, Expr) { return mk<NEQ>(a, b); }},
      {"ite", [](Expr a, Expr b, Expr c) { return mk<ITE>(a, b, c); }},
      {"ite bv", [&](Expr a, Expr, Expr) { return mk<ITE>(a, five, nine); }},
  };

  bz::Bitwuzla bzla(env.tm);
  unsigned checked = 0, disagreements = 0;
  for (auto &op : ops) {
    for (unsigned v = 0; v < 8; ++v) {
      Expr t = op.second(b[v & 1], b[(v >> 1) & 1], b[(v >> 2) & 1]);
      bz::Sort s = env.m.encode_term(t).sort();
      Expr r = s.is_bool() ? env.boolc("r") : env.bvc("r", s.bv_size());
      Expr expected = z3Value(z3, t, r);

      bzla.push(1);
      bzla.assert_formula(env.m.encode_term(mk<NEQ>(t, expected)));
      bool agrees = bzla.check_sat() == bz::Result::UNSAT;
      bzla.pop(1);
      ++checked;
      if (!agrees) {
        ++disagreements;
        MESSAGE(op.first << " " << v << ": z3 says "
                         << boost::lexical_cast<std::string>(*expected));
      }
    }
  }
  CHECK(checked == ops.size() * 8);
  CHECK(disagreements == 0);
}

namespace {
/// Random well-sorted formulas over Bool and bit-vector constants, for
/// differential testing against Z3. Subterms are reused within a formula, so
/// formulas are DAGs. Operators get as many arguments as Z3's encoder uses:
/// any number for and, or, bvadd, bvand, bvor and concat, two for the rest.
class RandomFormulas {
  Env &m_env;
  std::mt19937 m_rng;
  // -- the terms built for the current formula, by width; 0 is Bool
  std::map<unsigned, ExprVector> m_pool;
  // -- the arrays built for the current formula, by index and element width
  std::map<std::pair<unsigned, unsigned>, ExprVector> m_arrays;
  // -- the functions (lambdas) built for the current formula, likewise
  std::map<std::pair<unsigned, unsigned>, ExprVector> m_funcs;

public:
  /// also build stores into functions (only for the expansion test)
  bool m_function_stores = false;

private:

  unsigned pick(unsigned n) {
    return std::uniform_int_distribution<unsigned>(0, n - 1)(m_rng);
  }
  bool chance(unsigned percent) { return pick(100) < percent; }
  // -- the narrow width that the current formula favours: terms over the
  // -- same few constants make more formulas unsat or valid
  unsigned m_main = 1;
  unsigned width() {
    static const unsigned ws[] = {1, 2, 3, 4, 5, 8, 13, 16, 32, 64, 65, 128};
    if (chance(50))
      return m_main;
    return ws[pick(sizeof(ws) / sizeof(ws[0]))];
  }
  std::string bits(unsigned n) {
    std::string s;
    for (unsigned i = 0; i < n; ++i)
      s += pick(2) ? '1' : '0';
    return s;
  }
  Expr numeral(unsigned w) {
    switch (pick(4)) {
    case 0:
      return m_env.num(static_cast<long>(pick(3)) - 1, w); // -- -1, 0 or 1
    case 1: // -- the smallest or the largest signed value
      return bv::bvnum(pick(2)
                           ? expr::mpz_class("1" + std::string(w - 1, '0'), 2)
                           : expr::mpz_class("0" + std::string(w - 1, '1'), 2),
                       w, m_env.efac);
    case 2:
      return bv::bvnum(expr::mpz_class(bits(w), 2), w, m_env.efac);
    default: // -- out of range: negative or wider than w; taken modulo 2^w
      return bv::bvnum(expr::mpz_class((pick(2) ? "-" : "") + bits(w + 8), 2),
                       w, m_env.efac);
    }
  }
  /// small indices, so that every index can be written, and one like memory's
  unsigned indexWidth() {
    static const unsigned ws[] = {1, 2, 3, 32};
    return ws[pick(4)];
  }
  Expr reused(unsigned w) {
    ExprVector &p = m_pool[w];
    return p.empty() || !chance(60) ? Expr() : p[pick(p.size())];
  }
  ExprVector bvArgs(unsigned n, unsigned w, unsigned depth) {
    ExprVector args;
    for (unsigned i = 0; i < n; ++i)
      args.push_back(bv(w, depth));
    return args;
  }

public:
  RandomFormulas(Env &env, unsigned seed) : m_env(env), m_rng(seed) {}

  /// A conjunction of two to five random atoms; small widths and several
  /// conjuncts make a fair share of them unsat
  Expr formula() {
    m_pool.clear();
    m_arrays.clear();
    m_funcs.clear();
    m_main = 1 + pick(4);
    ExprVector conj;
    for (unsigned i = 0, n = 2 + pick(4); i < n; ++i)
      conj.push_back(boolean(3));
    // -- a definition of a constant, which Bitwuzla substitutes away; its
    // -- value then comes from the defining term
    if (chance(40)) {
      unsigned w = width();
      conj.push_back(pick(2) ? mk<EQ>(m_env.boolc("p" + std::to_string(pick(3))),
                                      boolean(3))
                             : mk<EQ>(m_env.bvc("x" + std::to_string(w) +
                                                    (pick(2) ? "a" : "b"),
                                                w),
                                      bv(w, 3)));
    }
    return conj.size() == 1 ? conj[0] : mknary<AND>(conj);
  }

  Expr boolean(unsigned depth) {
    if (Expr e = reused(0))
      return e;
    Expr e;
    unsigned d = depth - 1;
    if (depth == 0 || chance(15)) {
      e = chance(70) ? m_env.boolc("p" + std::to_string(pick(3)))
                     : (pick(2) ? mk<TRUE>(m_env.efac) : mk<FALSE>(m_env.efac));
    } else {
      static const std::vector<BinOp> bools = {
          binop<AND>(), binop<OR>(), binop<XOR>(), binop<IMPL>(),
          binop<IFF>(), binop<EQ>(), binop<NEQ>()};
      static const std::vector<BinOp> cmps = {
          binop<EQ>(),   binop<NEQ>(),  binop<BULT>(), binop<BULE>(),
          binop<BUGT>(), binop<BUGE>(), binop<BSLT>(), binop<BSLE>(),
          binop<BSGT>(), binop<BSGE>()};
      static const std::vector<BinOp> ovfs = {
          binop<UADD_NO_OVERFLOW>(), binop<USUB_NO_UNDERFLOW>(),
          binop<SADD_NO_OVERFLOW>(), binop<SADD_NO_UNDERFLOW>(),
          binop<SSUB_NO_OVERFLOW>(), binop<SSUB_NO_UNDERFLOW>(),
          binop<UMUL_NO_OVERFLOW>(), binop<SMUL_NO_OVERFLOW>(),
          binop<SMUL_NO_UNDERFLOW>()};
      unsigned w = width();
      switch (pick(10)) {
      case 0:
        e = mk<NEG>(boolean(d));
        break;
      case 1:
        e = pick(2)
                ? mknary<AND>(ExprVector{boolean(d), boolean(d), boolean(d)})
                : mknary<OR>(ExprVector{boolean(d), boolean(d), boolean(d)});
        break;
      case 2:
        e = bools[pick(bools.size())](boolean(d), boolean(d));
        break;
      case 3:
        e = mk<ITE>(boolean(d), boolean(d), boolean(d));
        break;
      case 4:
      case 5:
        e = cmps[pick(cmps.size())](bv(w, d), bv(w, d));
        break;
      case 6: {
        // -- equality of arrays; narrow elements, so that values repeat
        unsigned iw = indexWidth(), vw = 1 + pick(4);
        e = pick(2) ? mk<EQ>(array(iw, vw, d), array(iw, vw, d))
                    : mk<NEQ>(array(iw, vw, d), array(iw, vw, d));
        break;
      }
      // -- (no equality with a function: random ones made both solvers run
      // -- for minutes and Z3 undecided or wrong, so the formula check could
      // -- not judge them. The unit tests, SeaHorn's lambda-mode formulas in
      // -- the formula check, and the memphi examples have them.)
      case 7:
      case 8: {
        // -- a quantifier over a narrow bit-vector
        Expr x = boundConst(m_main);
        Expr body = cmps[pick(cmps.size())](mk<BADD>(x, bv(m_main, d)),
                                            bv(m_main, d));
        e = pick(2) ? bind::abs<FORALL>(ExprVector{x}, body)
                    : bind::abs<EXISTS>(ExprVector{x}, body);
        break;
      }
      default:
        // -- the multiplication tests only on narrow widths, to stay fast
        e = ovfs[pick(w <= 16 ? 9 : 6)](bv(w, d), bv(w, d));
        break;
      }
    }
    m_pool[0].push_back(e);
    return e;
  }

  Expr bv(unsigned w, unsigned depth) {
    if (Expr e = reused(w))
      return e;
    Expr e;
    unsigned d = depth - 1;
    if (depth == 0 || chance(15)) {
      e = chance(60)
              ? m_env.bvc("x" + std::to_string(w) + (pick(2) ? "a" : "b"), w)
              : numeral(w);
    } else {
      static const std::vector<BinOp> bins = {
          binop<BXOR>(), binop<BNAND>(), binop<BNOR>(),  binop<BXNOR>(),
          binop<BSUB>(), binop<BSHL>(),  binop<BLSHR>(), binop<BASHR>()};
      static const std::vector<BinOp> muls = {binop<BMUL>(),  binop<BUDIV>(),
                                              binop<BSDIV>(), binop<BUREM>(),
                                              binop<BSREM>(), binop<BSMOD>()};
      switch (pick(14)) {
      case 0:
        e = pick(2) ? mk<BNOT>(bv(w, d)) : mk<BNEG>(bv(w, d));
        break;
      case 12:
      case 13: {
        // -- the application of a function, by fapp or select
        unsigned iw = indexWidth();
        e = pick(2) ? mk<FAPP>(function(iw, w, d), bv(iw, d))
                    : op::array::select(function(iw, w, d), bv(iw, d));
        break;
      }
      case 10:
      case 11: {
        unsigned iw = indexWidth();
        e = op::array::select(array(iw, w, d), bv(iw, d));
        break;
      }
      case 1: {
        ExprVector args = bvArgs(2 + pick(2), w, d);
        switch (pick(3)) {
        case 0:
          e = mknary<BAND>(args);
          break;
        case 1:
          e = mknary<BOR>(args);
          break;
        default:
          e = mknary<BADD>(args);
          break;
        }
        break;
      }
      case 2:
        e = bins[pick(bins.size())](bv(w, d), bv(w, d));
        break;
      case 3:
        // -- multiplication and division only on narrow widths, to stay fast
        e = w <= 16 ? muls[pick(muls.size())](bv(w, d), bv(w, d))
                    : mk<BADD>(bv(w, d), bv(w, d));
        break;
      case 4:
        e = mk<ITE>(boolean(d), bv(w, d), bv(w, d));
        break;
      case 5: {
        unsigned ws = w + pick(9), lo = pick(ws - w + 1);
        e = bv::extract(lo + w - 1, lo, bv(ws, d));
        break;
      }
      case 6: {
        unsigned ws = 1 + pick(w); // -- the same width is allowed
        e = pick(2) ? bv::sext(bv(ws, d), w) : bv::zext(bv(ws, d), w);
        break;
      }
      case 7:
        if (w >= 2) {
          unsigned hi = 1 + pick(w - 1);
          e = mk<BCONCAT>(bv(hi, d), bv(w - hi, d));
          break;
        }
        e = pick(2) ? mk<BREDAND>(bv(width(), d)) : mk<BREDOR>(bv(width(), d));
        break;
      default:
        e = mk<BADD>(bv(w, d), bv(w, d));
        break;
      }
    }
    m_pool[w].push_back(e);
    return e;
  }

  /// The constant that the body of a lambda or quantifier over bit-vectors
  /// of width \p w uses for the variable, before abs makes it bound
  Expr boundConst(unsigned w) { return m_env.bvc("lx" + std::to_string(w), w); }
  /// (lambda x body), also when x does not occur in \p body
  Expr lambdaOf(Expr x, Expr body) {
    Expr r = bind::abs<LAMBDA>(ExprVector{x}, body);
    return isOpX<LAMBDA>(r) ? r : mk<LAMBDA>(bind::fname(x), body);
  }

  /// A function (a lambda) from bit-vectors of width \p iw to width \p vw
  Expr function(unsigned iw, unsigned vw, unsigned depth) {
    ExprVector &p = m_funcs[{iw, vw}];
    if (!p.empty() && chance(25))
      return p[pick(p.size())];
    Expr e;
    unsigned d = depth == 0 ? 0 : depth - 1;
    Expr x = boundConst(iw);
    if (m_function_stores && depth > 0 && chance(20)) {
      e = op::array::store(function(iw, vw, d), bv(iw, d), bv(vw, d));
    } else if (depth == 0 || chance(20)) {
      // -- an array wrapped as SeaHorn's lambda mode does, or a constant
      e = chance(70) ? lambdaOf(x, op::array::select(array(iw, vw, d), x))
                     : mk<LAMBDA>(m_env.bdecl("k", iw), bv(vw, d));
    } else {
      // -- (no store into a function: SeaHorn does not build one, unit tests
      // -- have it, and Z3 is incomplete on its own encoding of its
      // -- equality with an array)
      switch (pick(3)) {
      case 0: // -- a store, as SeaHorn's lambda memory builds it
        e = lambdaOf(x, mk<ITE>(mk<EQ>(x, bv(iw, d)), bv(vw, d),
                                mk<FAPP>(function(iw, vw, d), x)));
        break;
      case 1:
        e = mk<ITE>(boolean(d), function(iw, vw, d), function(iw, vw, d));
        break;
      default: // -- the variable anywhere in the body
        e = lambdaOf(x, mk<ITE>(mk<BULT>(x, bv(iw, d)), bv(vw, d),
                                mk<FAPP>(function(iw, vw, d),
                                         mk<BADD>(x, bv(iw, d)))));
        break;
      }
    }
    p.push_back(e);
    return e;
  }

  /// A formula with an equality or disequality between a function and a
  /// function or an array, over indices of 1-3 bits
  Expr withFunctionEquality() {
    Expr base = formula();
    unsigned iw = 1 + pick(3), vw = 1 + pick(4);
    Expr a = function(iw, vw, 3);
    Expr b = pick(2) ? function(iw, vw, 3) : array(iw, vw, 3);
    if (pick(2))
      std::swap(a, b);
    return mk<AND>(base, pick(2) ? mk<EQ>(a, b) : mk<NEQ>(a, b));
  }

  /// An array from bit-vectors of width \p iw to width \p vw
  Expr array(unsigned iw, unsigned vw, unsigned depth) {
    ExprVector &p = m_arrays[{iw, vw}];
    if (!p.empty() && chance(25))
      return p[pick(p.size())];
    Expr e;
    unsigned d = depth == 0 ? 0 : depth - 1;
    if (depth == 0 || chance(20)) {
      e = chance(75) ? m_env.arrc("A" + std::to_string(iw) + "_" +
                                      std::to_string(vw) + (pick(2) ? "a" : "b"),
                                  iw, vw)
                     : op::array::constArray(m_env.bvsort(iw), bv(vw, d));
    } else if (chance(75)) {
      e = op::array::store(array(iw, vw, d), bv(iw, d), bv(vw, d));
    } else {
      e = mk<ITE>(boolean(d), array(iw, vw, d), array(iw, vw, d));
    }
    p.push_back(e);
    return e;
  }
};

unsigned envOr(const char *name, unsigned dflt) {
  const char *v = std::getenv(name);
  return v ? static_cast<unsigned>(std::strtoul(v, nullptr, 10)) : dflt;
}

/// Bitwuzla 0.9.1 looks at its time limit only in the bit-vector solver,
/// not in its quantifier procedure, which can run on for hours (seen in the
/// 1.7 fuzzing). So a check of a formula with quantifiers is first run in a
/// child process, killed after \p ms of wall-clock time. If the child
/// finishes, the same (deterministic) check is run here, and its answer and
/// model are used; otherwise UNKNOWN, and \p timedOut is set.
SolverResult boundedCheck(Solver &s, unsigned ms, bool &timedOut) {
  timedOut = false;
  int fds[2];
  if (pipe(fds) != 0)
    return s.check();
  pid_t pid = fork();
  if (pid == 0) {
    close(fds[0]);
    char c = static_cast<char>(s.check());
    ssize_t w = write(fds[1], &c, 1);
    (void)w;
    _exit(0);
  }
  close(fds[1]);
  struct pollfd pfd = {fds[0], POLLIN, 0};
  char c;
  bool done = pid > 0 && poll(&pfd, 1, static_cast<int>(ms)) > 0 &&
              read(fds[0], &c, 1) == 1;
  if (pid > 0) {
    if (!done)
      kill(pid, SIGKILL);
    waitpid(pid, nullptr, 0);
  }
  close(fds[0]);
  if (!done) {
    timedOut = true;
    return SolverResult::UNKNOWN;
  }
  return s.check();
}
} // namespace

TEST_CASE("bitwuzla.random formulas agree with z3") {
  // -- BITWUZLA_FUZZ_N formulas from seed BITWUZLA_FUZZ_SEED; each formula f
  // -- and its negation are solved by the adapter and by Z3. Every sat answer
  // -- is also certified: Z3 checks f under Bitwuzla's values of f's constants.
  // -- Bitwuzla may answer unknown, but only on an equality of arrays with a
  // -- const-array (it does not fully support those).
  Env env;
  EZ3 z3(env.efac);
  RandomFormulas gen(env, envOr("BITWUZLA_FUZZ_SEED", 1));
  const unsigned n = envOr("BITWUZLA_FUZZ_N", 300);
  // -- Z3's time limit for each formula check
  const unsigned check_ms = envOr("BITWUZLA_FUZZ_CHECK_MS", 10000);

  // -- one adapter for every formula: reset() must clear everything. Each
  // -- check is limited (quantifiers can make either solver run long); a
  // -- check that runs out is unknown.
  const unsigned solve_ms = envOr("BITWUZLA_FUZZ_SOLVE_MS", 5000);
  const unsigned wall_ms = 4 * solve_ms;
  bitwuzla_solver_impl adapter(solve_ms);
  Solver &s = adapter;
  ZParams<EZ3> zparams(z3);
  zparams.set("timeout", solve_ms);
  // -- quantified checks killed after wall_ms (boundedCheck)
  unsigned bw_timeouts = 0;

  unsigned sat = 0, unsat = 0, z3_unknown = 0, disagreements = 0,
           bad_models = 0;
  // -- Bitwuzla's unknowns, and those on a formula without an equality of
  // -- arrays and a const-array; formulas with an array
  unsigned bw_unknown = 0, unexplained_unknown = 0, with_arrays = 0;
  // -- plan 1.7: formulas with a lambda, with a quantifier (for Bitwuzla);
  // -- Z3's unknowns on formulas without one; functions given no value
  unsigned with_lambdas = 0, with_quantifiers = 0, z3_unknown_plain = 0,
           functions_refused = 0;
  // -- formulas the encoder rejects (none should be)
  unsigned not_encoded = 0;
  // -- terms evaluated through the model; values that are not values, or not
  // -- in [0, 2^w); values that differ from Z3's under the same assignment
  unsigned evaluated = 0, non_values = 0, value_mismatches = 0;
  // -- of those, arrays compared by Z3; terms with an array equality, which
  // -- must give nondet, and those that gave something else
  unsigned arrays_compared = 0, refused = 0, not_refused = 0;
  // -- sat models with no values (an equality of narrow arrays in f)
  unsigned refused_models = 0;
  // -- verdicts of the formula check (translation validation) on every f
  std::map<EncodingVerdict, unsigned> encoding;
  Expr f;
  for (unsigned i = 0; i < 2 * n; ++i) {
    f = i % 2 == 0 ? gen.formula() : mk<NEG>(f);
    if (anySubterm(f, [](Expr x) { return isOpX<SELECT>(x) || isArrayTerm(x); }))
      ++with_arrays;
    if (anySubterm(f, [](Expr x) { return isOpX<LAMBDA>(x); }))
      ++with_lambdas;
    const bool quantified = needsQuantifier(f);
    if (quantified)
      ++with_quantifiers;

    // -- every generated formula must encode. Caught here: an UnsupportedExpr
    // -- that escaped the test case would outlive env's ExprFactory and crash
    bz::Term ft;
    try {
      ft = env.m.encode_term(f);
    } catch (UnsupportedExpr &ex) {
      ++not_encoded;
      MESSAGE("formula " << i << ": not encoded: " << ex.what());
      continue;
    }
    auto ec = checkBitwuzlaEncoding(f, ft, check_ms, &env.tm);
    ++encoding[ec.verdict];
    if (ec.verdict != EncodingVerdict::SAME)
      MESSAGE("formula " << i << ": encoding check says "
                         << std::string(verdictName(ec.verdict)) << ": "
                         << ec.detail << "\n  formula: " << *f);

    // -- BITWUZLA_FUZZ_TRACE=1 prints each formula before it is solved
    if (envOr("BITWUZLA_FUZZ_TRACE", 0))
      llvm::errs() << "formula " << i << ": " << *f << "\n";
    s.reset();
    REQUIRE(s.add(f));
    bool timedOut = false;
    SolverResult r = quantified ? boundedCheck(s, wall_ms, timedOut) : s.check();
    if (timedOut)
      ++bw_timeouts;
    ZSolver<EZ3> zs(z3);
    zs.set(zparams);
    zs.assertExpr(f);
    boost::tribool zr = zs.solve();
    if (boost::indeterminate(zr)) {
      // -- Z3 is incomplete with quantifiers; nothing else may be unknown
      ++z3_unknown;
      if (!quantified) {
        ++z3_unknown_plain;
        MESSAGE("formula " << i << ": unknown to z3");
      }
      continue;
    }
    if (r == SolverResult::UNKNOWN) {
      ++bw_unknown;
      if (!quantified && (!hasArrayEquality(f) || !anySubterm(f, [](Expr x) {
                            return isOpX<CONST_ARRAY>(x);
                          }))) {
        ++unexplained_unknown;
        MESSAGE("formula " << i << ": Bitwuzla answers unknown");
      }
      continue;
    }
    if (r != (zr ? SolverResult::SAT : SolverResult::UNSAT)) {
      ++disagreements;
      MESSAGE("formula " << i << " (seed " << envOr("BITWUZLA_FUZZ_SEED", 1)
                         << "): z3 says " << (zr ? "sat" : "unsat"));
      continue;
    }
    if (r == SolverResult::UNSAT) {
      ++unsat;
      continue;
    }
    ++sat;

    // -- with an equality of narrow arrays in f, or a quantifier, the model
    // -- must have no values at all (Bitwuzla may give constants wrong ones,
    // -- or solve again while values are read)
    if (hasNarrowArrayEquality(f) || quantified) {
      ++refused_models;
      Solver::model_ref model = s.get_model();
      ExprSet seen;
      ExprVector terms;
      termsOf(f, seen, terms);
      for (Expr t : terms) {
        if (isOpX<NONDET>(model->eval(t, true)))
          ++refused;
        else {
          ++not_refused;
          MESSAGE("formula " << i << ": the model gives a value for " << *t
                             << ", with an equality of narrow arrays in the "
                                "formula");
        }
      }
      continue;
    }

    // -- the model, through the Solver interface. Evaluate every term of f,
    // -- and two terms over constants that are in no assertion (Bitwuzla
    // -- completes its model, so they get values too). complete alternates.
    Solver::model_ref model = s.get_model();
    ExprSet seen;
    ExprVector terms;
    termsOf(f, seen, terms);
    std::vector<std::pair<Expr, Expr>> values; // -- term, Bitwuzla's value
    Expr someBv, someBool, someSel, freshArr;
    for (Expr t : terms) {
      Expr v = model->eval(t, values.size() % 2 == 0);
      values.push_back({t, v});
      unsigned w;
      if (!someBv && bv::isBvNum(v, w)) {
        someBv = mk<BADD>(t, env.bvc("fresh" + std::to_string(w), w));
        freshArr = env.arrc("freshA" + std::to_string(w), w, 8);
        someSel = op::array::select(freshArr, t);
      }
      if (!someBool && (isOpX<TRUE>(v) || isOpX<FALSE>(v)))
        someBool = mk<XOR>(t, env.boolc("fresh"));
    }
    for (Expr t : {someBv, someBool, someSel, freshArr})
      if (t)
        values.push_back({t, model->eval(t, false)});

    // -- the values of the constants, those in no assertion included, must
    // -- satisfy f for Z3
    ExprSet consts;
    for (auto &tv : values)
      filter(tv.first, bind::IsConst(), std::inserter(consts, consts.begin()));
    ZSolver<EZ3> certify(z3);
    certify.set(zparams);
    certify.assertExpr(f);
    bool all_values = true;
    for (Expr c : consts) {
      Expr v = model->eval(c, true);
      // -- Z3 cannot take nondet (it would exit); count it below instead
      if (!(isOpX<TRUE>(v) || isOpX<FALSE>(v) || bv::is_bvnum(v) ||
            isArrayValue(v))) {
        all_values = false;
        break;
      }
      certify.assertExpr(mk<EQ>(c, v));
    }
    if (!all_values) {
      ++non_values;
      MESSAGE("formula " << i << ": the model has no value for a constant");
      continue;
    }
    boost::tribool ok = certify.solve();
    if (!ok || boost::indeterminate(ok)) {
      ++bad_models;
      MESSAGE("formula " << i << ": z3 rejects Bitwuzla's values");
      continue;
    }

    // -- and under those values, Z3 must give every term the same value
    ZModel<EZ3> zmodel = certify.getModel();
    for (auto &tv : values) {
      ++evaluated;
      Expr v = tv.second;
      if (isFunctionTerm(tv.first)) {
        // -- a function has no value (plan 1.7)
        if (isOpX<NONDET>(v)) {
          ++functions_refused;
        } else {
          ++not_refused;
          MESSAGE("formula " << i << ": the model gives " << *v
                             << " for the function " << *tv.first);
        }
        continue;
      }
      if (hasArrayEquality(tv.first)) {
        // -- Bitwuzla can get these wrong, so the model must not answer
        if (isOpX<NONDET>(v)) {
          ++refused;
        } else {
          ++not_refused;
          MESSAGE("formula " << i << ": the model gives " << *v << " for "
                             << *tv.first << ", which has an array equality");
        }
        continue;
      }
      if (isArrayValue(v)) {
        // -- Z3 proves the term equal to the value, under the same values of
        // -- the constants (they fix the term)
        ++arrays_compared;
        certify.push();
        certify.assertExpr(mk<NEQ>(tv.first, v));
        boost::tribool differ = certify.solve();
        certify.pop();
        if (differ || boost::indeterminate(differ)) {
          ++value_mismatches;
          MESSAGE("formula " << i << ": " << *tv.first << " is " << *v
                             << " in Bitwuzla's model, but not for z3");
        }
        continue;
      }
      if (!(isOpX<TRUE>(v) || isOpX<FALSE>(v) || isUnsignedBvNum(v))) {
        ++non_values;
        MESSAGE("formula " << i << ": the model gives " << *v << " for "
                           << *tv.first);
        continue;
      }
      Expr zv = zmodel.eval(tv.first, true);
      if (!sameValue(v, zv)) {
        ++value_mismatches;
        MESSAGE("formula " << i << ": " << *tv.first << " is " << *v
                           << " in Bitwuzla's model, but " << *zv << " for z3");
      }
    }
  }
  MESSAGE((2 * n) << " formulas: " << sat << " sat, " << unsat << " unsat, "
                  << z3_unknown << " unknown to z3, " << bw_unknown
                  << " unknown to Bitwuzla (" << unexplained_unknown
                  << " unexplained), " << with_arrays
                  << " with arrays; encoding check: "
                  << encoding[EncodingVerdict::SAME] << " same; model: "
                  << evaluated << " terms evaluated (" << arrays_compared
                  << " arrays), " << value_mismatches << " differ from z3, "
                  << non_values << " not values, " << refused
                  << " refused (array equality), " << not_refused
                  << " not refused; " << refused_models
                  << " sat models without values (narrow array equality or "
                     "quantifier); "
                  << with_lambdas << " with lambdas, " << with_quantifiers
                  << " with quantifiers, " << functions_refused
                  << " functions without value; " << bw_timeouts
                  << " quantified checks killed after " << wall_ms << " ms");
  // -- every formula Bitwuzla got is Z3's formula, not only equisatisfiable
  CHECK(encoding[EncodingVerdict::SAME] == 2 * n);
  CHECK(not_encoded == 0);
  CHECK(sat + unsat + z3_unknown + bw_unknown + disagreements + not_encoded ==
        2 * n);
  CHECK(disagreements == 0);
  // -- unknown only where Bitwuzla says it is incomplete, and rarely
  CHECK(unexplained_unknown == 0);
  CHECK(bw_unknown <= 2 * n / 10);
  CHECK(not_refused == 0);
  CHECK(bad_models == 0);
  CHECK(z3_unknown_plain == 0);
  CHECK(non_values == 0);
  CHECK(value_mismatches == 0);
  // -- every sat formula has at least one term
  CHECK(evaluated >= sat);
  // -- the generator must produce both kinds, and arrays, or the test proves
  // -- little
  // -- (of the 2n formulas: a quarter each; until 1.6 this was an eighth)
  CHECK(sat >= 2 * n / 4);
  CHECK(unsat >= 2 * n / 4);
  CHECK(with_arrays >= 2 * n / 4);
  CHECK(with_lambdas >= 2 * n / 4);
  CHECK(with_quantifiers >= 2 * n / 10);
}

namespace {
/// The index width of a function or array term built by the fuzzer
unsigned functionIndexWidth(Expr f) {
  if (isOpX<LAMBDA>(f))
    return bv::width(bind::boundSort(f, 0));
  if (isOpX<ITE>(f))
    return functionIndexWidth(f->arg(1));
  if (isOpX<STORE>(f))
    return functionIndexWidth(f->arg(0));
  return indexWidthOf(f);
}

/// \p e with each equality or disequality that has a function on a side
/// replaced by one equality per index (2^w of them), so that Z3 gets no
/// equality between lambdas, on which it is incomplete and even wrong
Expr expandFunctionEqualities(Expr e, ExprMap &cache) {
  auto it = cache.find(e);
  if (it != cache.end())
    return it->second;
  Expr res = e;
  if ((isOpX<EQ>(e) || isOpX<NEQ>(e)) &&
      (isFunctionTerm(e->arg(0)) || isFunctionTerm(e->arg(1)))) {
    Expr a = expandFunctionEqualities(e->arg(0), cache);
    Expr b = expandFunctionEqualities(e->arg(1), cache);
    unsigned w = functionIndexWidth(isFunctionTerm(a) ? a : b);
    ExprVector eqs;
    for (unsigned i = 0; i < (1u << w); ++i) {
      Expr idx = bv::bvnum(expr::mpz_class(i), w, e->efac());
      eqs.push_back(mk<EQ>(op::array::select(a, idx), op::array::select(b, idx)));
    }
    Expr all = eqs.size() == 1 ? eqs[0] : mknary<AND>(eqs);
    res = isOpX<EQ>(e) ? all : mk<NEG>(all);
  } else if (e->arity() > 0) {
    ExprVector args;
    bool changed = false;
    for (unsigned i = 0, sz = e->arity(); i < sz; ++i) {
      args.push_back(expandFunctionEqualities(e->arg(i), cache));
      changed |= args.back() != e->arg(i);
    }
    if (changed)
      res = e->efac().mkNary(e->op(), args);
  }
  cache.insert({e, res});
  return res;
}
} // namespace

TEST_CASE("bitwuzla.function equalities against an expansion") {
  // -- plan 1.7, after the review: random formulas with an equality between a
  // -- function and a function or array, over indices of 1-3 bits, and with
  // -- stores into functions. Bitwuzla gets each equality as a forall; Z3
  // -- gets the formula with the equality expanded over every index.
  Env env;
  EZ3 z3(env.efac);
  RandomFormulas gen(env, envOr("BITWUZLA_FUZZ_SEED", 1) + 1000);
  gen.m_function_stores = true;
  const unsigned n = envOr("BITWUZLA_FUZZ_N", 300) / 2;
  const unsigned solve_ms = envOr("BITWUZLA_FUZZ_SOLVE_MS", 5000);
  const unsigned wall_ms = 4 * solve_ms;
  bitwuzla_solver_impl adapter(solve_ms);
  Solver &s = adapter;
  ZParams<EZ3> zparams(z3);
  zparams.set("timeout", solve_ms);
  unsigned bw_timeouts = 0;
  unsigned agree = 0, disagree = 0, bw_unknown = 0, z3_unknown = 0, sat = 0,
           unsat = 0;
  Expr f;
  for (unsigned i = 0; i < 2 * n; ++i) {
    f = i % 2 == 0 ? gen.withFunctionEquality() : mk<NEG>(f);
    ExprMap cache;
    Expr g = expandFunctionEqualities(f, cache);
    REQUIRE(g != f);
    s.reset();
    REQUIRE(s.add(f));
    bool timedOut = false;
    SolverResult r = boundedCheck(s, wall_ms, timedOut);
    if (timedOut)
      ++bw_timeouts;
    ZSolver<EZ3> zs(z3);
    zs.set(zparams);
    zs.assertExpr(g);
    boost::tribool zr = zs.solve();
    if (boost::indeterminate(zr)) {
      ++z3_unknown;
      continue;
    }
    if (r == SolverResult::UNKNOWN) {
      ++bw_unknown;
      continue;
    }
    if (r == (zr ? SolverResult::SAT : SolverResult::UNSAT)) {
      ++agree;
      ++(zr ? sat : unsat);
    } else {
      ++disagree;
      MESSAGE("formula " << i << ": z3 says " << (zr ? "sat" : "unsat")
                         << " on the expansion of " << *f);
    }
  }
  MESSAGE((2 * n) << " formulas with function equalities: " << agree
                  << " agree with z3 on the expansion (" << sat << " sat, "
                  << unsat << " unsat), " << disagree << " disagree, "
                  << bw_unknown << " unknown to Bitwuzla (" << bw_timeouts
                  << " killed after " << wall_ms << " ms), " << z3_unknown
                  << " unknown to z3");
  CHECK(disagree == 0);
  // -- both answers, and few unknowns, or the test proves little
  CHECK(sat >= 2 * n / 10);
  CHECK(unsat >= 2 * n / 10);
  CHECK(agree >= 2 * n * 8 / 10);
}

TEST_CASE("bitwuzla.encoding check") {
  // -- translation validation: Bitwuzla prints its term, Z3 parses it and
  // -- compares it with SeaHorn's own Z3 encoding of the same Expr
  Env env;
  Expr x = env.bvc("x", 8), y = env.bvc("y", 8);
  auto verdict = [&](Expr e, const bz::Term &t) {
    auto ec = checkBitwuzlaEncoding(e, t, 10000);
    INFO(verdictName(ec.verdict) << ": " << ec.detail);
    return ec.verdict;
  };
  auto own = [&](Expr e) { return verdict(e, env.m.encode_term(e)); };

  // -- the encoder's own terms, for every operator on 8 bits
  const std::vector<BinOp> ops = {
      binop<BADD>(),  binop<BSUB>(),   binop<BMUL>(),  binop<BUDIV>(),
      binop<BSDIV>(), binop<BUREM>(),  binop<BSREM>(), binop<BSMOD>(),
      binop<BAND>(),  binop<BOR>(),    binop<BXOR>(),  binop<BNAND>(),
      binop<BNOR>(),  binop<BXNOR>(),  binop<BSHL>(),  binop<BLSHR>(),
      binop<BASHR>(), binop<BCONCAT>()};
  for (auto &op : ops)
    CHECK(own(op(x, y)) == EncodingVerdict::SAME);
  const std::vector<BinOp> preds = {binop<EQ>(),
                                    binop<NEQ>(),
                                    binop<BULT>(),
                                    binop<BULE>(),
                                    binop<BUGT>(),
                                    binop<BUGE>(),
                                    binop<BSLT>(),
                                    binop<BSLE>(),
                                    binop<BSGT>(),
                                    binop<BSGE>(),
                                    binop<SADD_NO_OVERFLOW>(),
                                    binop<SADD_NO_UNDERFLOW>(),
                                    binop<UADD_NO_OVERFLOW>(),
                                    binop<SSUB_NO_OVERFLOW>(),
                                    binop<SSUB_NO_UNDERFLOW>(),
                                    binop<USUB_NO_UNDERFLOW>(),
                                    binop<SMUL_NO_OVERFLOW>(),
                                    binop<SMUL_NO_UNDERFLOW>(),
                                    binop<UMUL_NO_OVERFLOW>()};
  for (auto &op : preds)
    CHECK(own(op(x, y)) == EncodingVerdict::SAME);
  CHECK(own(mk<BNOT>(x)) == EncodingVerdict::SAME);
  CHECK(own(mk<BNEG>(x)) == EncodingVerdict::SAME);
  CHECK(own(bv::extract(6, 2, x)) == EncodingVerdict::SAME);
  CHECK(own(bv::sext(x, 13)) == EncodingVerdict::SAME);
  CHECK(own(bv::zext(x, 13)) == EncodingVerdict::SAME);
  CHECK(own(env.num(-3, 8)) == EncodingVerdict::SAME);
  Expr p = env.boolc("p"), q = env.boolc("q");
  CHECK(own(mk<ITE>(p, x, y)) == EncodingVerdict::SAME);
  CHECK(own(mk<IMPL>(p, q)) == EncodingVerdict::SAME);
  CHECK(own(mk<IFF>(p, q)) == EncodingVerdict::SAME);
  CHECK(own(mk<XOR>(p, q)) == EncodingVerdict::SAME);

  // -- a wrong term is caught: unsigned and signed comparison differ
  bz::Term tx = env.m.encode_term(x), ty = env.m.encode_term(y);
  CHECK(verdict(mk<BULT>(x, y), env.tm.mk_term(bz::Kind::BV_SLT, {tx, ty})) ==
        EncodingVerdict::DIFFERENT);
  // -- and so are swapped arguments of a non-commutative operator
  CHECK(verdict(mk<BSUB>(x, y), env.tm.mk_term(bz::Kind::BV_SUB, {ty, tx})) ==
        EncodingVerdict::DIFFERENT);
  // -- but not swapped arguments of a commutative one
  CHECK(verdict(mk<BADD>(x, y), env.tm.mk_term(bz::Kind::BV_ADD, {ty, tx})) ==
        EncodingVerdict::SAME);
  // -- sorts must agree: wider, narrower, Bool against bit-vector
  CHECK(verdict(x, env.m.encode_term(env.bvc("x", 16))) ==
        EncodingVerdict::DIFFERENT);
  CHECK(verdict(env.bvc("x", 16), tx) == EncodingVerdict::DIFFERENT);
  Expr pb = env.boolc("pb");
  CHECK(verdict(pb, tx) == EncodingVerdict::DIFFERENT);
  CHECK(verdict(x, env.m.encode_term(pb)) == EncodingVerdict::DIFFERENT);
  // -- a constant that Z3's encoding does not have makes them differ
  CHECK(verdict(x, env.tm.mk_const(env.tm.mk_bv_sort(8), "z")) ==
        EncodingVerdict::DIFFERENT);
  // -- two constants with one name cannot be told apart in SMT-LIB
  bz::Term x16 = env.m.encode_term(env.bvc("x", 16));
  CHECK(verdict(mk<EQ>(x, x),
                env.tm.mk_term(bz::Kind::EQUAL,
                               {tx, env.tm.mk_term(bz::Kind::BV_EXTRACT, {x16},
                                                   {7, 0})})) ==
        EncodingVerdict::UNCHECKED);
  // -- also with the same sort: merging two such constants would make
  // -- (= x x') look valid, and so equal to Z3's encoding of (= x x)
  bz::Term other = env.tm.mk_const(env.tm.mk_bv_sort(8), "x");
  CHECK(verdict(mk<EQ>(x, x), env.tm.mk_term(bz::Kind::EQUAL, {tx, other})) ==
        EncodingVerdict::UNCHECKED);

  // -- Z3's encoder keeps only two factors of an n-ary bvmul
  // -- (ExprToZ.def, case BMUL), while Bitwuzla's term has all three
  Expr z = env.bvc("z", 8);
  CHECK(own(mknary<BMUL>(ExprVector{x, y, z})) == EncodingVerdict::DIFFERENT);
}

TEST_CASE("bitwuzla.encoding check: when it cannot compare") {
  Env env;
  Expr x = env.bvc("x", 8), y = env.bvc("y", 8);
  bz::Sort bv8 = env.tm.mk_bv_sort(8);
  auto verdict = [&](Expr e, const bz::Term &t, unsigned ms = 10000) {
    auto ec = checkBitwuzlaEncoding(e, t, ms);
    INFO(verdictName(ec.verdict) << ": " << ec.detail);
    return ec;
  };

  CHECK(std::string(verdictName(EncodingVerdict::SAME)) == "SAME");
  CHECK(std::string(verdictName(EncodingVerdict::DIFFERENT)) == "DIFFERENT");
  CHECK(std::string(verdictName(EncodingVerdict::UNDECIDED)) == "UNDECIDED");
  CHECK(std::string(verdictName(EncodingVerdict::UNCHECKED)) == "UNCHECKED");

  // -- terms the check does not handle are reported, not guessed
  CHECK(verdict(x, env.tm.mk_var(bv8, "v")).verdict ==
        EncodingVerdict::UNCHECKED);
  CHECK(verdict(x, env.tm.mk_const(bv8)).verdict == EncodingVerdict::UNCHECKED);
  // -- since plan 1.6, constants of array sort are compared: x is not a[y]
  bz::Sort arr = env.tm.mk_array_sort(bv8, bv8);
  bz::Term a = env.tm.mk_const(arr, "a");
  CHECK(verdict(x, env.tm.mk_term(bz::Kind::ARRAY_SELECT,
                                  {a, env.m.encode_term(y)}))
            .verdict == EncodingVerdict::DIFFERENT);
  // -- but not a term of array sort, nor arrays with other index or element
  // -- sorts
  CHECK(
      verdict(x, env.tm.mk_const_array(arr, env.tm.mk_bv_zero(bv8))).verdict ==
      EncodingVerdict::UNCHECKED);
  bz::Sort boolS = env.tm.mk_bool_sort();
  bz::Term byBool = env.tm.mk_const(env.tm.mk_array_sort(boolS, bv8), "bb");
  CHECK(verdict(x, env.tm.mk_term(bz::Kind::ARRAY_SELECT,
                                  {byBool, env.tm.mk_true()}))
            .verdict == EncodingVerdict::UNCHECKED);
  bz::Term nested = env.tm.mk_const(env.tm.mk_array_sort(bv8, arr), "nn");
  bz::Term inner = env.tm.mk_term(bz::Kind::ARRAY_SELECT,
                                  {nested, env.m.encode_term(y)});
  CHECK(verdict(x, env.tm.mk_term(bz::Kind::ARRAY_SELECT,
                                  {inner, env.m.encode_term(y)}))
            .verdict == EncodingVerdict::UNCHECKED);

  // -- a constant may have the name of the check's own helper constant
  Expr clash = env.bvc("encoding_check_rhs", 8);
  CHECK(verdict(mk<BADD>(clash, x), env.m.encode_term(mk<BADD>(clash, x)))
            .verdict == EncodingVerdict::SAME);
  // -- also when only Z3's side has it: e = c against the wrong term #x00
  // -- must not compare c with itself
  CHECK(verdict(clash, env.tm.mk_bv_zero(bv8)).verdict ==
        EncodingVerdict::DIFFERENT);
  // -- wherever the constant is: here only in the last argument, where
  // -- comparing ite(p, y, c) with y would be valid if rhs were c
  Expr pc = env.boolc("pc");
  CHECK(verdict(mk<ITE>(pc, y, clash), env.m.encode_term(y)).verdict ==
        EncodingVerdict::DIFFERENT);

  // -- names that SMT-LIB cannot carry safely are not compared
  for (const char *odd : {"a|b", "|x|", "a\\b", "_let0"}) {
    Expr c = env.bvc(odd, 8);
    INFO("name " << odd);
    CHECK(verdict(mk<BADD>(c, x), env.m.encode_term(mk<BADD>(c, x))).verdict ==
          EncodingVerdict::UNCHECKED);
  }
  // -- nor operators that SeaHorn's Z3 encoder lacks (it fails on them)
  Expr rep2 = mk<BREPEAT>(mkTerm<unsigned>(2, env.efac), env.num(0xA, 4));
  auto ec2 = verdict(rep2, env.m.encode_term(rep2));
  CHECK(ec2.verdict == EncodingVerdict::UNCHECKED);
  CHECK(ec2.detail.find("repeat") != std::string::npos);
  Expr rot = mk<BROTATE_LEFT>(mkTerm<unsigned>(1, env.efac), x);
  CHECK(verdict(rot, env.m.encode_term(rot)).verdict ==
        EncodingVerdict::UNCHECKED);
  Expr rotr = mk<BROTATE_RIGHT>(mkTerm<unsigned>(1, env.efac), x);
  CHECK(verdict(rotr, env.m.encode_term(rotr)).verdict ==
        EncodingVerdict::UNCHECKED);
  // -- also below the root, in any argument
  Expr deep = mk<EQ>(rep2, env.bvc("r", 8));
  CHECK(verdict(deep, env.m.encode_term(deep)).verdict ==
        EncodingVerdict::UNCHECKED);

  // -- text that Z3 cannot read, or that is more than one term
  CHECK(checkSmtLibTermWithZ3(x, "(bvfoo x)", {{"x", 8}}, 8, 10000).verdict ==
        EncodingVerdict::UNCHECKED);
  CHECK(checkSmtLibTermWithZ3(x, "x)) (assert (= x x", {{"x", 8}}, 8, 10000)
            .verdict == EncodingVerdict::UNCHECKED);

  // -- Z3 gives up: x = (x udiv y) * y + (x urem y) holds for every y, but
  // -- proving it at 64 bits takes far longer than a millisecond
  Expr p = env.bvc("p", 64), q = env.bvc("q", 64);
  bz::Term tp = env.m.encode_term(p), tq = env.m.encode_term(q);
  bz::Term roundtrip = env.tm.mk_term(
      bz::Kind::BV_ADD,
      {env.tm.mk_term(bz::Kind::BV_MUL,
                      {env.tm.mk_term(bz::Kind::BV_UDIV, {tp, tq}), tq}),
       env.tm.mk_term(bz::Kind::BV_UREM, {tp, tq})});
  CHECK(verdict(p, roundtrip, 1).verdict == EncodingVerdict::UNDECIDED);

  // -- the differing values are cut to a readable length
  ExprVector many;
  for (unsigned k = 0; k < 40; ++k)
    many.push_back(env.bvc("c" + std::to_string(k), 8));
  Expr sum = mknary<BADD>(many);
  bz::Term off = env.tm.mk_term(
      bz::Kind::BV_ADD, {env.m.encode_term(sum), env.tm.mk_bv_one(bv8)});
  auto ec = verdict(sum, off);
  CHECK(ec.verdict == EncodingVerdict::DIFFERENT);
  CHECK(ec.detail.size() < 500);
  CHECK(ec.detail.substr(ec.detail.size() - 3) == "...");
}

TEST_CASE("bitwuzla.encoding check option") {
  // -- --horn-bw-check-encoding=FILE makes the adapter check every formula
  // -- and append one line per add() to FILE
  auto &registered = llvm::cl::getRegisteredOptions();
  REQUIRE(registered.count("horn-bw-check-encoding"));
  auto *opt = static_cast<llvm::cl::opt<std::string> *>(
      registered["horn-bw-check-encoding"]);
  std::string path =
      std::string(std::getenv("TMPDIR") ? std::getenv("TMPDIR") : "/tmp") +
      "/units_bitwuzla_check_encoding.log";
  std::remove(path.c_str());
  // -- switched off again however the test ends, for the other tests
  struct Reset {
    llvm::cl::opt<std::string> *o;
    ~Reset() { *o = ""; }
  } reset{opt};
  *opt = path;

  Env env;
  Expr x = env.bvc("x", 8);
  Expr i = bind::intConst(mkTerm<std::string>("i", env.efac));
  bitwuzla_solver_impl adapter;
  Solver &s = adapter;
  CHECK(s.add(mk<BULT>(x, env.num(3, 8))));
  CHECK(s.add(mk<EQ>(mk<BADD>(x, x), env.num(4, 8))));
  CHECK_FALSE(s.add(mk<EQ>(i, i)));
  CHECK(s.check() == SolverResult::UNKNOWN);

  std::ifstream in(path);
  std::vector<std::string> verdicts;
  for (std::string line; std::getline(in, line);)
    verdicts.push_back(line.substr(0, line.find('\t')));
  CHECK(verdicts == std::vector<std::string>{"SAME", "SAME", "NOT-ENCODED"});
  std::remove(path.c_str());
}

TEST_CASE("bitwuzla.repeat, rotate and n-ary operators") {
  // -- Z3's marshal has no repeat or rotate, so these check exact values
  Env env;
  auto u = [&](unsigned n) { return mkTerm<unsigned>(n, env.efac); };
  Expr x81 = env.num(0x81, 8);
  CHECK(
      env.valid(mk<EQ>(mk<BREPEAT>(u(2), env.num(0xA, 4)), env.num(0xAA, 8))));
  CHECK(env.valid(mk<EQ>(mk<BROTATE_LEFT>(u(1), x81), env.num(0x03, 8))));
  CHECK(env.valid(mk<EQ>(mk<BROTATE_RIGHT>(u(1), x81), env.num(0xC0, 8))));
  // -- rotating by the width or more wraps around
  CHECK(env.valid(mk<EQ>(mk<BROTATE_LEFT>(u(8), x81), x81)));
  CHECK(env.valid(mk<EQ>(mk<BROTATE_LEFT>(u(9), x81), env.num(0x03, 8))));

  // -- n-ary forms of the associative operators
  Expr x = env.bvc("x", 8), y = env.bvc("y", 8), z = env.bvc("z", 8);
  CHECK(env.valid(
      mk<EQ>(mknary<BMUL>(ExprVector{x, y, z}), mk<BMUL>(x, mk<BMUL>(y, z)))));
  CHECK(env.valid(
      mk<EQ>(mknary<BAND>(ExprVector{x, y, z}), mk<BAND>(x, mk<BAND>(y, z)))));
  CHECK(env.valid(
      mk<EQ>(mknary<BOR>(ExprVector{x, y, z}), mk<BOR>(x, mk<BOR>(y, z)))));
  CHECK(env.valid(
      mk<EQ>(mknary<BXOR>(ExprVector{x, y, z}), mk<BXOR>(x, mk<BXOR>(y, z)))));
  // -- with one argument they are the identity (Bitwuzla wants two or more)
  Expr p = env.boolc("p");
  for (Expr e1 :
       {mknary<BADD>(ExprVector{x}), mknary<BMUL>(ExprVector{x}),
        mknary<BAND>(ExprVector{x}), mknary<BOR>(ExprVector{x}),
        mknary<BXOR>(ExprVector{x}), mknary<BCONCAT>(ExprVector{x})}) {
    CHECK(e1->arity() == 1);
    CHECK(env.valid(mk<EQ>(e1, x)));
  }
  for (Expr e1 : {mknary<AND>(ExprVector{p}), mknary<OR>(ExprVector{p}),
                  mknary<XOR>(ExprVector{p})}) {
    CHECK(e1->arity() == 1);
    CHECK(env.valid(mk<IFF>(e1, p)));
  }
  // -- the others take two arguments in Bitwuzla
  Expr sub3 = mknary<BSUB>(ExprVector{x, y, z});
  CHECK(env.rejects(mk<EQ>(sub3, x), sub3));
}

TEST_CASE("bitwuzla.unsupported") {
  Env env;
  Expr x = env.bvc("x", 8);
  Expr i = bind::intConst(mkTerm<std::string>("i", env.efac));

  // -- the error names the unsupported operator, not one of its arguments
  Expr i2b = mk<INT2BV>(mkTerm<unsigned>(8, env.efac), i);
  CHECK(env.rejects(mk<AND>(mk<EQ>(x, x), mk<BULT>(i2b, x)), i2b));
  Expr b2i = mk<BV2INT>(x);
  CHECK(env.rejects(mk<EQ>(b2i, b2i), b2i));
  Expr rot = mk<BEXT_ROTATE_LEFT>(x, env.num(1, 8));
  CHECK(env.rejects(mk<EQ>(rot, x), rot));
  Expr leq = mk<LEQ>(x, x);
  CHECK(env.rejects(mk<OR>(leq, mk<EQ>(x, x)), leq));
  // -- constants of unsupported sorts: integers, arrays other than from
  // -- bit-vectors to bit-vectors
  CHECK(env.rejects(mk<EQ>(i, i), i));
  Expr p0 = env.boolc("p0");
  Expr byBool = bind::mkConst(mkTerm<std::string>("byBool", env.efac),
                              sort::arrayTy(sort::boolTy(env.efac),
                                            env.bvsort(8)));
  CHECK(env.rejects(mk<EQ>(op::array::select(byBool, p0), x), byBool));
  Expr toBool = bind::mkConst(mkTerm<std::string>("toBool", env.efac),
                              sort::arrayTy(env.bvsort(8),
                                            sort::boolTy(env.efac)));
  CHECK(env.rejects(op::array::select(toBool, x), toBool));
  // -- and constant arrays of them
  Expr caBool = op::array::constArray(sort::boolTy(env.efac), x);
  CHECK(env.rejects(mk<EQ>(op::array::select(caBool, p0), x), caBool));
  Expr caToBool = op::array::constArray(env.bvsort(8), p0);
  CHECK(env.rejects(op::array::select(caToBool, x), caToBool));
  Expr caInt = op::array::constArray(sort::intTy(env.efac), x);
  CHECK(env.rejects(mk<EQ>(caInt, caInt), caInt));
  // -- array operators other than select, store and const-array
  Expr A = env.arrc("A", 8, 8);
  Expr dflt = op::array::aDefault(A);
  CHECK(env.rejects(mk<EQ>(dflt, x), dflt));
  Expr asArr = mk<AS_ARRAY>(A);
  CHECK(env.rejects(mk<EQ>(op::array::select(asArr, x), x), asArr));
  Expr g = bind::fdecl(mkTerm<std::string>("g", env.efac),
                       ExprVector{env.bvsort(8), env.bvsort(8)});
  Expr amap = mk<ARRAY_MAP>(g, A);
  CHECK(env.rejects(mk<EQ>(op::array::select(amap, x), x), amap));
  // -- uninterpreted functions
  Expr f = bind::fdecl(mkTerm<std::string>("f", env.efac),
                       ExprVector{env.bvsort(8), env.bvsort(8)});
  Expr fx = bind::fapp(f, x);
  CHECK(env.rejects(mk<EQ>(fx, x), fx));
  // -- a bound variable outside of any binder
  Expr b0 = bind::bvar(0, env.bvsort(8));
  CHECK(env.rejects(mk<EQ>(b0, x), b0));
  // -- =>, <=>, = and distinct take exactly two arguments: chained, they have
  // -- no agreed meaning (Bitwuzla, SeaHorn's evaluator and Z3's encoder
  // differ)
  Expr p = env.boolc("p"), q = env.boolc("q");
  for (Expr e3 :
       {mknary<IMPL>(ExprVector{p, q, p}), mknary<IFF>(ExprVector{p, q, p}),
        mknary<EQ>(ExprVector{x, x, x}), mknary<NEQ>(ExprVector{x, x, x})})
    CHECK(env.rejects(mk<OR>(e3, p), e3));
  // -- Bitwuzla's own errors also become UnsupportedExpr, naming the term:
  // -- here a width of 0
  Expr z0 = env.num(0, 0), c0 = env.bvc("c0", 0);
  CHECK(env.rejects(mk<EQ>(z0, z0), z0));
  CHECK(env.rejects(mk<EQ>(c0, c0), c0));
  CHECK_THROWS_AS(env.m.encode_sort(env.bvsort(0)), UnsupportedExpr);

  // -- the encoder still works after a rejection
  CHECK(env.valid(mk<EQ>(mk<BADD>(x, env.num(0, 8)), x)));

  // -- the message stays short for a large DAG: printed as a tree, this one
  // -- has 2^64 nodes (memset.symbolic.unaligned in test/opsem hung on that)
  Expr big = x;
  for (unsigned k = 0; k < 64; ++k)
    big = mk<BADD>(big, big);
  Expr bigrot = mk<BEXT_ROTATE_LEFT>(big, x);
  try {
    env.m.encode_term(mk<EQ>(bigrot, x));
    FAIL("rotation by a term is not supported");
  } catch (UnsupportedExpr &ex) {
    CHECK(ex.expr() == bigrot);
    CHECK(std::string(ex.what()).find("bvextrotleft(bvadd(...), x)") !=
          std::string::npos);
  }
  // -- and at most four arguments are printed
  Expr wide = mknary<NEQ>(ExprVector{big, x, x, x, x});
  try {
    env.m.encode_term(wide);
    FAIL("distinct with five arguments is not supported");
  } catch (UnsupportedExpr &ex) {
    CHECK(ex.expr() == wide);
    CHECK(std::string(ex.what()).find("x, x, x, ...)") != std::string::npos);
  }

  // -- extension to a narrower sort
  Expr narrow = mk<BZEXT>(x, env.bvsort(4));
  CHECK(env.rejects(mk<EQ>(narrow, env.num(0, 4)), narrow));
  // -- repeat and rotate take an unsigned numeral, not a bit-vector one
  Expr rep2 = mk<BREPEAT>(env.num(2, 8), x);
  CHECK(env.rejects(mk<EQ>(rep2, env.bvc("y", 16)), rep2));
}

TEST_CASE("bitwuzla.deep expressions") {
  // -- the encoder uses an explicit stack: a chain deeper than the default
  // -- recursion limits of a naive encoder must not overflow
  Env env;
  Expr x = env.bvc("x", 32);
  Expr e = x;
  const unsigned depth = 100000;
  for (unsigned k = 0; k < depth; ++k)
    e = mk<BADD>(e, env.num(1, 32));
  CHECK(env.valid(mk<EQ>(e, mk<BADD>(x, env.num(depth, 32)))));
}

// -- the solver adapter, through the generic Solver interface

TEST_CASE("bitwuzla.solver") {
  Env env;
  bitwuzla_solver_impl bzla;
  Solver &s = bzla;
  CHECK(s.get_kind() == seahorn::solver::SolverKind::BITWUZLA);
  Expr x = env.bvc("x", 8);

  // -- x + 1 = 0 is sat (with x = 255); adding x = 0 makes it unsat
  CHECK(s.add(mk<EQ>(mk<BADD>(x, env.num(1, 8)), env.num(0, 8))));
  CHECK(s.check() == SolverResult::SAT);
  CHECK(s.add(mk<EQ>(x, env.num(0, 8))));
  CHECK(s.check() == SolverResult::UNSAT);

  // -- reset removes every assertion
  s.reset();
  CHECK(s.check() == SolverResult::SAT);
  CHECK(s.add(mk<EQ>(x, env.num(7, 8))));
  CHECK(s.check() == SolverResult::SAT);
  CHECK(s.add(mk<BULT>(x, env.num(7, 8))));
  CHECK(s.check() == SolverResult::UNSAT);
}

TEST_CASE("bitwuzla.solver unsupported input") {
  Env env;
  bitwuzla_solver_impl bzla;
  Solver &s = bzla;
  Expr x = env.bvc("x", 8);
  CHECK(s.add(mk<EQ>(x, env.num(1, 8))));

  // -- an assertion that cannot be encoded: add() says so, and since callers
  // -- (SolverBmc) ignore that, checks answer unknown, never sat or unsat
  Expr i = bind::intConst(mkTerm<std::string>("i", env.efac));
  CHECK_FALSE(s.add(mk<EQ>(mk<BV2INT>(x), i)));
  CHECK(s.check() == SolverResult::UNKNOWN);
  CHECK(s.add(mk<EQ>(x, env.num(2, 8)))); // unsat with the first one
  CHECK(s.check() == SolverResult::UNKNOWN);

  // -- reset removes it
  s.reset();
  CHECK(s.check() == SolverResult::SAT);

  // -- a term that Bitwuzla itself rejects (width 0)
  CHECK_FALSE(s.add(mk<EQ>(env.num(0, 0), env.num(0, 0))));
  CHECK(s.check() == SolverResult::UNKNOWN);
  s.reset();
  CHECK(s.check() == SolverResult::SAT);

  // -- a non-Boolean assertion
  CHECK_FALSE(s.add(x));
  CHECK(s.check() == SolverResult::UNKNOWN);
  s.reset();
  CHECK(s.add(mk<EQ>(x, env.num(2, 8))));
  CHECK(s.check() == SolverResult::SAT);
}

// -- models (plan 1.5)

TEST_CASE("bitwuzla.model values") {
  Env env;
  bitwuzla_solver_impl bzla;
  Solver &s = bzla;
  Expr x = env.bvc("x", 8), y = env.bvc("y", 8), b = env.bvc("b", 1),
       w = env.bvc("w", 128), p = env.boolc("p"), q = env.boolc("q");
  CHECK(s.add(mk<EQ>(mk<BADD>(x, env.num(1, 8)), env.num(0, 8))));
  CHECK(s.add(mk<EQ>(b, env.num(1, 1))));
  CHECK(s.add(mk<EQ>(w, env.num(-1, 128))));
  CHECK(s.add(p));
  CHECK(s.add(mk<NEG>(q)));
  REQUIRE(s.check() == SolverResult::SAT);
  Solver::model_ref m = s.get_model();

  // -- numerals are hash-consed: == compares the number and the width. The
  // -- number is the unsigned reading of the bits.
  Expr ones128 =
      bv::bvnum(expr::mpz_class(std::string(128, '1'), 2), 128, env.efac);
  CHECK(m->eval(x, false) == env.num(255, 8));
  CHECK(m->eval(b, false) == env.num(1, 1));
  CHECK(m->eval(w, false) == ones128);
  CHECK(m->eval(p, false) == mk<TRUE>(env.efac));
  CHECK(m->eval(q, false) == mk<FALSE>(env.efac));

  // -- terms, not only constants
  CHECK(m->eval(mk<BADD>(x, env.num(1, 8)), false) == env.num(0, 8));
  CHECK(m->eval(mk<BULT>(x, env.num(7, 8)), false) == mk<FALSE>(env.efac));
  CHECK(m->eval(mk<OR>(p, q), false) == mk<TRUE>(env.efac));
  CHECK(m->eval(bv::extract(7, 4, x), false) == env.num(15, 4));

  // -- complete makes no difference
  for (Expr t : {x, b, w, p, q, mk<BADD>(x, w)})
    CHECK(m->eval(t, true) == m->eval(t, false));

  // -- y is in no assertion: it gets a value, the same each time, and terms
  // -- over it agree with that value (the values are one assignment)
  Expr vy = m->eval(y, false);
  REQUIRE(bv::is_bvnum(vy));
  CHECK(m->eval(y, true) == vy);
  expr::mpz_class y_minus_x = (bv::toMpz(vy) + expr::mpz_class(1ul)) % 256u;
  CHECK(m->eval(mk<BSUB>(y, x), false) == bv::bvnum(y_minus_x, 8, env.efac));
  Expr r = env.boolc("r"); // -- also in no assertion
  Expr vr = m->eval(r, false);
  CHECK((isOpX<TRUE>(vr) || isOpX<FALSE>(vr)));
  CHECK(m->eval(mk<AND>(r, p), false) == vr);

  // -- evaluating does not change the solver: y and r got values above, but
  // -- they are still free
  CHECK(s.add(mk<EQ>(y, mk<BADD>(vy, env.num(5, 8)))));
  CHECK(s.add(isOpX<TRUE>(vr) ? mk<NEG>(r) : r));
  REQUIRE(s.check() == SolverResult::SAT);
  Solver::model_ref m2 = s.get_model();
  CHECK(m2->eval(y, true) != vy);
  CHECK(m2->eval(r, true) != vr);
  CHECK(m2->eval(x, true) == env.num(255, 8));
}

TEST_CASE("bitwuzla.model after a change") {
  // -- a model is valid only until the next add, check or reset; after that,
  // -- and if the last check was not sat, it gives nondet, never a value
  Env env;
  Expr x = env.bvc("x", 8);
  auto noValue = [&](const Solver::model_ref &m) {
    return isOpX<NONDET>(m->eval(x, true)) && isOpX<NONDET>(m->eval(x, false));
  };
  bitwuzla_solver_impl bzla;
  Solver &s = bzla;

  CHECK(noValue(s.get_model())); // -- before any check
  CHECK(s.add(mk<EQ>(x, env.num(3, 8))));
  CHECK(noValue(s.get_model())); // -- added since the last check
  REQUIRE(s.check() == SolverResult::SAT);
  Solver::model_ref m1 = s.get_model();
  CHECK(m1->eval(x, true) == env.num(3, 8));

  // -- a later add
  CHECK(s.add(mk<BULT>(x, env.num(5, 8))));
  CHECK(noValue(m1));
  // -- a later check, even a sat one: m1 stays out of date, m2 is valid
  REQUIRE(s.check() == SolverResult::SAT);
  CHECK(noValue(m1));
  Solver::model_ref m2 = s.get_model();
  CHECK(m2->eval(x, true) == env.num(3, 8));
  // -- a check with nothing added in between
  REQUIRE(s.check() == SolverResult::SAT);
  CHECK(noValue(m2));

  // -- reset, then a different formula: an old model must not show its values
  Solver::model_ref m3 = s.get_model();
  CHECK(m3->eval(x, true) == env.num(3, 8));
  s.reset();
  CHECK(noValue(m3));
  CHECK(s.add(mk<EQ>(x, env.num(9, 8))));
  REQUIRE(s.check() == SolverResult::SAT);
  CHECK(noValue(m3));
  CHECK(s.get_model()->eval(x, true) == env.num(9, 8));

  // -- after unsat
  CHECK(s.add(mk<EQ>(x, env.num(4, 8))));
  REQUIRE(s.check() == SolverResult::UNSAT);
  CHECK(noValue(s.get_model()));

  // -- after unknown (an assertion it cannot encode)
  s.reset();
  Expr i = bind::intConst(mkTerm<std::string>("i", env.efac));
  CHECK_FALSE(s.add(mk<EQ>(mk<BV2INT>(x), i)));
  REQUIRE(s.check() == SolverResult::UNKNOWN);
  CHECK(noValue(s.get_model()));

  // -- after the solver is destroyed
  Solver::model_ref orphan;
  {
    bitwuzla_solver_impl gone;
    CHECK(gone.add(mk<EQ>(x, env.num(3, 8))));
    REQUIRE(gone.check() == SolverResult::SAT);
    orphan = gone.get_model();
    CHECK(orphan->eval(x, true) == env.num(3, 8));
  }
  CHECK(noValue(orphan));

  // -- printing an out-of-date model prints no values
  for (const Solver::model_ref &m : {m1, orphan}) {
    std::string str;
    llvm::raw_string_ostream os(str);
    m->print(os);
    CHECK(os.str().empty());
  }
}

TEST_CASE("bitwuzla.model after an assertion it cannot encode") {
  // -- Bitwuzla never sees an assertion that the encoder rejects, nor a check
  // -- that answers unknown because of one, so it still holds the old sat
  // -- model and would answer from it. Only the adapter can tell that the
  // -- model is out of date.
  Env env;
  bitwuzla_solver_impl bzla;
  Solver &s = bzla;
  Expr x = env.bvc("x", 8);
  auto noValue = [&](const Solver::model_ref &m) {
    return isOpX<NONDET>(m->eval(x, true));
  };
  CHECK(s.add(mk<EQ>(x, env.num(3, 8))));
  REQUIRE(s.check() == SolverResult::SAT);
  Solver::model_ref m = s.get_model();
  CHECK(m->eval(x, true) == env.num(3, 8));

  Expr i = bind::intConst(mkTerm<std::string>("i", env.efac));
  CHECK_FALSE(s.add(mk<EQ>(mk<BV2INT>(x), i)));
  CHECK(noValue(m));
  REQUIRE(s.check() == SolverResult::UNKNOWN);
  CHECK(noValue(m));
  CHECK(noValue(s.get_model()));
}

TEST_CASE("bitwuzla.model of terms it cannot evaluate") {
  Env env;
  bitwuzla_solver_impl bzla;
  Solver &s = bzla;
  Expr x = env.bvc("x", 8);
  CHECK(s.add(mk<EQ>(x, env.num(3, 8))));
  REQUIRE(s.check() == SolverResult::SAT);
  Solver::model_ref m = s.get_model();

  // -- terms the encoder rejects give nondet
  Expr i = bind::intConst(mkTerm<std::string>("i", env.efac));
  Expr a = bind::mkConst(mkTerm<std::string>("a", env.efac),
                         sort::arrayTy(sort::boolTy(env.efac), env.bvsort(8)));
  Expr A = env.arrc("A", 8, 8);
  CHECK(isOpX<NONDET>(m->eval(i, true)));
  CHECK(isOpX<NONDET>(m->eval(mk<BV2INT>(x), true)));
  CHECK(isOpX<NONDET>(m->eval(a, true)));
  CHECK(isOpX<NONDET>(m->eval(mk<SELECT>(a, mk<TRUE>(env.efac)), false)));
  CHECK(isOpX<NONDET>(m->eval(op::array::aDefault(A), false)));
  // -- a struct is evaluated field by field (bitwuzla.model of structs); a
  // -- struct sort elsewhere is rejected
  Expr st = bind::mkConst(mkTerm<std::string>("st", env.efac),
                          sort::structTy(env.bvsort(8), env.bvsort(8)));
  CHECK(isOpX<NONDET>(m->eval(st, false)));
  CHECK(isOpX<NONDET>(m->eval(strct::extractVal(st, 0), false)));

  // -- the model and the solver still work
  CHECK(m->eval(x, true) == env.num(3, 8));
  CHECK(s.add(mk<EQ>(x, env.num(4, 8))));
  CHECK(s.check() == SolverResult::UNSAT);
}

TEST_CASE("bitwuzla.decode values") {
  Env env;
  bz::TermManager &tm = env.tm;
  bz::Sort bv8 = tm.mk_bv_sort(8);
  auto decode = [&](const bz::Term &t) {
    return decode_bitwuzla_value(t, env.efac);
  };
  CHECK(decode(tm.mk_true()) == mk<TRUE>(env.efac));
  CHECK(decode(tm.mk_false()) == mk<FALSE>(env.efac));
  CHECK(decode(tm.mk_bv_value(bv8, "255", 10)) == env.num(255, 8));
  CHECK(decode(tm.mk_bv_value(bv8, "-1", 10)) == env.num(255, 8));
  CHECK(decode(tm.mk_bv_zero(tm.mk_bv_sort(1))) == env.num(0, 1));
  CHECK(decode(tm.mk_bv_one(tm.mk_bv_sort(1))) == env.num(1, 1));
  CHECK(decode(tm.mk_bv_value(tm.mk_bv_sort(128), std::string(128, '1'))) ==
        bv::bvnum(expr::mpz_class(std::string(128, '1'), 2), 128, env.efac));
  CHECK(decode(tm.mk_bv_value(tm.mk_bv_sort(65), "1" + std::string(64, '0'))) ==
        bv::bvnum(expr::mpz_class(1ul) << 64, 65, env.efac));

  // -- not a value, or a value of another sort: a null Expr
  CHECK_FALSE(decode(tm.mk_const(bv8, "c")));
  CHECK_FALSE(decode(tm.mk_var(bv8, "v")));
  CHECK_FALSE(decode(tm.mk_const(tm.mk_bool_sort(), "p")));
  CHECK_FALSE(decode(
      tm.mk_term(bz::Kind::BV_ADD, {tm.mk_bv_one(bv8), tm.mk_bv_one(bv8)})));
  CHECK_FALSE(decode(tm.mk_rm_value(bz::RoundingMode::RNE)));
  CHECK_FALSE(decode(tm.mk_fp_pos_zero(tm.mk_fp_sort(5, 11))));

  // -- arrays (plan 1.6): a chain of stores over a constant array, rebuilt
  // -- in the same order, with unsigned numerals
  bz::Sort bv2 = tm.mk_bv_sort(2), arr = tm.mk_array_sort(bv2, bv8);
  auto bwv = [&](bz::Sort s, unsigned n) {
    return tm.mk_bv_value_uint64(s, n);
  };
  bz::Term ca = tm.mk_const_array(arr, bwv(bv8, 255));
  Expr eca = op::array::constArray(env.bvsort(2), env.num(255, 8));
  CHECK(decode(ca) == eca);
  bz::Term st1 = tm.mk_term(bz::Kind::ARRAY_STORE, {ca, bwv(bv2, 3), bwv(bv8, 1)});
  bz::Term st2 =
      tm.mk_term(bz::Kind::ARRAY_STORE, {st1, bwv(bv2, 0), bwv(bv8, 128)});
  Expr est1 = op::array::store(eca, env.num(3, 2), env.num(1, 8));
  CHECK(decode(st1) == est1);
  CHECK(decode(st2) == op::array::store(est1, env.num(0, 2), env.num(128, 8)));
  // -- an index stored twice keeps both stores, so the last one still wins
  bz::Term st3 =
      tm.mk_term(bz::Kind::ARRAY_STORE, {st1, bwv(bv2, 3), bwv(bv8, 2)});
  CHECK(decode(st3) == op::array::store(est1, env.num(3, 2), env.num(2, 8)));
  // -- anything that is not made of values: a null Expr
  bz::Term ac = tm.mk_const(arr, "ac");
  bz::Term c8 = tm.mk_const(bv8, "c8"), c2 = tm.mk_const(bv2, "c2");
  CHECK_FALSE(decode(ac));
  CHECK_FALSE(decode(tm.mk_const_array(arr, c8)));
  CHECK_FALSE(decode(tm.mk_term(bz::Kind::ARRAY_STORE, {ac, bwv(bv2, 1), bwv(bv8, 1)})));
  CHECK_FALSE(decode(tm.mk_term(bz::Kind::ARRAY_STORE, {ca, c2, bwv(bv8, 1)})));
  CHECK_FALSE(decode(tm.mk_term(bz::Kind::ARRAY_STORE, {st1, bwv(bv2, 1), c8})));
  CHECK_FALSE(decode(tm.mk_term(
      bz::Kind::ITE, {tm.mk_const(tm.mk_bool_sort(), "pp"), ca, st1})));
  // -- an index sort other than a bit-vector
  CHECK_FALSE(decode(tm.mk_const_array(
      tm.mk_array_sort(tm.mk_bool_sort(), bv8), bwv(bv8, 0))));
}

TEST_CASE("bitwuzla.model print") {
  Env env;
  bitwuzla_solver_impl bzla;
  Solver &s = bzla;
  Expr x = env.bvc("x", 8), p = env.boolc("p"), q = env.boolc("q");
  auto str = [](Expr e) { return boost::lexical_cast<std::string>(*e); };
  auto printed = [](const Solver::model_ref &m) {
    std::string out;
    llvm::raw_string_ostream os(out);
    m->print(os);
    return os.str();
  };

  // -- every constant of the assertions, once, sorted by name
  CHECK(s.add(mk<EQ>(mk<BADD>(x, env.num(1, 8)), env.num(0, 8))));
  CHECK(s.add(mk<OR>(p, mk<EQ>(x, x))));
  CHECK(s.add(p));
  REQUIRE(s.check() == SolverResult::SAT);
  CHECK(printed(s.get_model()) == "p = " + str(mk<TRUE>(env.efac)) +
                                      "\nx = " + str(env.num(255, 8)) + "\n");

  // -- an out-of-date model prints nothing, also while the solver has
  // -- assertions and a newer sat model
  Solver::model_ref old = s.get_model();
  CHECK(s.add(mk<NEG>(q)));
  CHECK(printed(old).empty());
  CHECK(printed(s.get_model()).empty()); // -- added since the last check
  REQUIRE(s.check() == SolverResult::SAT);
  CHECK(printed(old).empty());
  CHECK_FALSE(printed(s.get_model()).empty());

  // -- after reset, only the new assertions' constants
  s.reset();
  CHECK(s.add(mk<NEG>(q)));
  REQUIRE(s.check() == SolverResult::SAT);
  CHECK(printed(s.get_model()) == "q = " + str(mk<FALSE>(env.efac)) + "\n");
}


namespace {
/// Z3 proves \p e valid
bool z3Valid(EZ3 &z3, Expr e) {
  ZSolver<EZ3> zs(z3);
  zs.assertExpr(mk<NEG>(e));
  boost::tribool r = zs.solve();
  return bool(!r) && !boost::indeterminate(r);
}

/// The adapter's answer on the conjunction of \p fs, in a fresh solver
SolverResult adapterCheck(std::initializer_list<Expr> fs) {
  bitwuzla_solver_impl bzla;
  Solver &s = bzla;
  for (Expr f : fs)
    REQUIRE(s.add(f));
  return s.check();
}
} // namespace

TEST_CASE("bitwuzla.arrays") {
  Env env;
  using namespace op::array;
  const SolverResult SAT = SolverResult::SAT, UNSAT = SolverResult::UNSAT;
  // -- read over write, like memory (64-bit index, 8-bit elements), and with
  // -- a 2-bit index
  for (unsigned iw : {64u, 2u}) {
    INFO("index width " << iw);
    Expr a = env.arrc("a" + std::to_string(iw), iw, 8);
    Expr i = env.bvc("i" + std::to_string(iw), iw);
    Expr j = env.bvc("j" + std::to_string(iw), iw);
    Expr v = env.bvc("v", 8);
    Expr st = store(a, i, v);
    CHECK(adapterCheck({mk<NEQ>(select(st, i), v)}) == UNSAT);
    CHECK(adapterCheck({mk<NEQ>(i, j), mk<NEQ>(select(st, j), select(a, j))}) ==
          UNSAT);
    CHECK(adapterCheck({mk<NEQ>(select(st, j), select(a, j))}) == SAT);
    // -- two writes to the same place: the second one wins (mem.c)
    Expr st2 = store(store(a, i, env.num(1, 8)), j, env.num(2, 8));
    CHECK(adapterCheck({mk<NEQ>(select(st2, i), env.num(1, 8))}) == SAT);
    CHECK(adapterCheck({mk<NEQ>(i, j), mk<NEQ>(select(st2, i), env.num(1, 8))}) ==
          UNSAT);
    // -- extensionality
    Expr b = env.arrc("b" + std::to_string(iw), iw, 8);
    CHECK(adapterCheck({mk<EQ>(a, b), mk<NEQ>(select(a, i), select(b, i))}) ==
          UNSAT);
    CHECK(adapterCheck({mk<NEQ>(a, b)}) == SAT);
    // -- ite over arrays
    Expr p = env.boolc("p");
    CHECK(adapterCheck({p, mk<NEQ>(select(mk<ITE>(p, a, b), i), select(a, i))}) ==
          UNSAT);
  }

  // -- constant arrays
  Expr i2 = env.bvc("i2", 2), k = env.bvc("k", 8);
  Expr c3 = constArray(env.bvsort(2), env.num(3, 8));
  CHECK(env.valid(mk<EQ>(select(c3, i2), env.num(3, 8))));
  CHECK(env.valid(mk<EQ>(select(constArray(env.bvsort(64), k),
                                env.bvc("i64", 64)),
                         k)));
  // -- writing 7 at all four indices of a 2-bit array gives the constant
  // -- array 7 ...
  Expr all7 = c3;
  for (unsigned n = 0; n < 4; ++n)
    all7 = store(all7, env.num(n, 2), env.num(7, 8));
  Expr c7 = constArray(env.bvsort(2), env.num(7, 8));
  CHECK(adapterCheck({mk<NEQ>(all7, c7)}) == UNSAT);
  // -- ... but three of them do not
  Expr three7 = store(store(store(c3, env.num(0, 2), env.num(7, 8)),
                            env.num(1, 2), env.num(7, 8)),
                      env.num(2, 2), env.num(7, 8));
  CHECK(adapterCheck({mk<NEQ>(three7, c7)}) == SAT);

  // -- Bitwuzla 0.9.1 answers unknown on an equality of two constant
  // -- arrays; the adapter passes that on, whether the formula is sat or not
  Expr ck = constArray(env.bvsort(8), k);
  Expr c3b = constArray(env.bvsort(8), env.num(3, 8));
  CHECK(adapterCheck({mk<EQ>(ck, c3b)}) == SolverResult::UNKNOWN);
  CHECK(adapterCheck({mk<EQ>(ck, c3b), mk<EQ>(k, env.num(4, 8))}) ==
        SolverResult::UNKNOWN);
}

TEST_CASE("bitwuzla.array operators it cannot encode") {
  Env env;
  bitwuzla_solver_impl bzla;
  Solver &s = bzla;
  Expr x = env.bvc("x", 8), A = env.arrc("A", 8, 8);
  Expr byBool = bind::mkConst(
      mkTerm<std::string>("byBool", env.efac),
      sort::arrayTy(sort::boolTy(env.efac), env.bvsort(8)));
  Expr g = bind::fdecl(mkTerm<std::string>("g", env.efac),
                       ExprVector{env.bvsort(8), env.bvsort(8)});
  for (Expr bad :
       {mk<EQ>(op::array::aDefault(A), x),
        mk<EQ>(op::array::select(mk<AS_ARRAY>(A), x), x),
        mk<EQ>(op::array::select(mk<ARRAY_MAP>(g, A), x), x),
        mk<EQ>(op::array::select(byBool, mk<TRUE>(env.efac)), x)}) {
    INFO(*bad);
    // -- with an assertion that is unsat on its own: never unsat, nor sat
    CHECK(s.add(mk<NEQ>(op::array::select(op::array::store(A, x, x), x), x)));
    CHECK_FALSE(s.add(bad));
    CHECK(s.check() == SolverResult::UNKNOWN);
    s.reset();
    CHECK(s.add(mk<EQ>(op::array::select(A, x), x)));
    CHECK(s.check() == SolverResult::SAT);
    s.reset();
  }
}

TEST_CASE("bitwuzla.model of arrays") {
  Env env;
  EZ3 z3(env.efac);
  using namespace op::array;
  for (unsigned iw : {8u, 64u}) {
    INFO("index width " << iw);
    bitwuzla_solver_impl bzla;
    Solver &s = bzla;
    Expr a = env.arrc("a", iw, 8), i = env.bvc("i", iw);
    CHECK(s.add(mk<EQ>(select(a, env.num(1, iw)), env.num(5, 8))));
    CHECK(s.add(mk<EQ>(select(a, env.num(2, iw)), env.num(7, 8))));
    CHECK(s.add(mk<EQ>(select(a, i), env.num(9, 8))));
    REQUIRE(s.check() == SolverResult::SAT);
    Solver::model_ref m = s.get_model();

    // -- a store chain of numerals over a constant array of a numeral
    Expr va = m->eval(a, true);
    Expr cur = va;
    unsigned stores = 0;
    while (isOpX<STORE>(cur)) {
      CHECK(isUnsignedBvNum(cur->arg(1)));
      CHECK(isUnsignedBvNum(cur->arg(2)));
      cur = cur->arg(0);
      ++stores;
    }
    REQUIRE(isOpX<CONST_ARRAY>(cur));
    CHECK(cur->arg(0) == env.bvsort(iw));
    CHECK(isUnsignedBvNum(cur->arg(1)));
    CHECK(stores >= 2);
    // -- that Z3 proves has the asserted values
    Expr vi = m->eval(i, false);
    CHECK(z3Valid(z3, mk<AND>(mk<EQ>(select(va, env.num(1, iw)), env.num(5, 8)),
                              mk<EQ>(select(va, env.num(2, iw)), env.num(7, 8)),
                              mk<EQ>(select(va, vi), env.num(9, 8)))));
    // -- terms of array sort and selects
    CHECK(m->eval(select(a, env.num(1, iw)), true) == env.num(5, 8));
    CHECK(m->eval(select(a, i), false) == env.num(9, 8));
    Expr st = store(a, env.num(1, iw), env.num(6, 8));
    Expr vst = m->eval(st, false);
    CHECK(z3Valid(z3, mk<AND>(mk<EQ>(select(vst, env.num(1, iw)), env.num(6, 8)),
                              mk<EQ>(select(vst, env.num(2, iw)), env.num(7, 8)))));
    // -- an array in no assertion gets a value too, consistent with terms
    // -- over it
    Expr fresh = env.arrc("fresh", iw, 8);
    Expr vf = m->eval(fresh, true);
    REQUIRE(isOpX<CONST_ARRAY>(vf));
    CHECK(m->eval(select(fresh, i), true) == vf->arg(1));

    // -- the guards of 1.5 hold for array terms: after a change, nondet
    CHECK(s.add(mk<EQ>(select(a, env.num(3, iw)), env.num(1, 8))));
    CHECK(isOpX<NONDET>(m->eval(a, true)));
    CHECK(isOpX<NONDET>(m->eval(select(a, i), true)));
    REQUIRE(s.check() == SolverResult::SAT);
    CHECK(isOpX<NONDET>(m->eval(a, true)));
    CHECK(isOpX<NONDET>(s.get_model()->eval(mk<EQ>(a, a), true)));
    CHECK_FALSE(isOpX<NONDET>(s.get_model()->eval(a, true)));
  }
}

TEST_CASE("bitwuzla.model does not evaluate array equalities") {
  Env env;
  using namespace op::array;
  bitwuzla_solver_impl bzla;
  Solver &s = bzla;
  Expr p = env.boolc("p"), x = env.bvc("x", 8);
  Expr a = env.arrc("a", 1, 8), b = env.arrc("b", 1, 8);
  CHECK(s.add(p));
  CHECK(s.add(mk<EQ>(select(a, env.num(0, 1)), env.num(5, 8))));
  CHECK(s.add(mk<EQ>(select(a, env.num(1, 1)), env.num(5, 8))));
  CHECK(s.add(mk<EQ>(x, env.num(1, 8))));
  REQUIRE(s.check() == SolverResult::SAT);
  Solver::model_ref m = s.get_model();

  // -- probe16c: Bitwuzla's value of these is false, but they are true
  Expr c3 = constArray(env.bvsort(2), env.num(3, 8));
  Expr all7 = c3;
  for (unsigned n = 0; n < 4; ++n)
    all7 = store(all7, env.num(n, 2), env.num(7, 8));
  Expr c7 = constArray(env.bvsort(2), env.num(7, 8));
  Expr c5 = constArray(env.bvsort(1), env.num(5, 8));
  for (Expr e : {mk<EQ>(all7, c7), mk<EQ>(a, c5), mk<NEQ>(a, c5),
                 mk<AND>(p, mk<EQ>(a, c5)),
                 mk<ITE>(mk<EQ>(a, b), x, env.num(2, 8)), mk<EQ>(a, a)}) {
    INFO(*e);
    CHECK(isOpX<NONDET>(m->eval(e, true)));
    CHECK(isOpX<NONDET>(m->eval(e, false)));
  }
  // -- other terms still have values, and the solver still works
  CHECK(m->eval(mk<AND>(p, mk<EQ>(select(a, env.num(1, 1)), env.num(5, 8))),
                false) == mk<TRUE>(env.efac));
  CHECK(m->eval(x, false) == env.num(1, 8));
  // -- a is 5 at both of its indices, so it equals the constant array 5:
  // -- asserted, the disequality is unsat (Bitwuzla answers unknown on the
  // -- equality itself, see bitwuzla.arrays)
  CHECK(s.add(mk<NEQ>(a, c5)));
  CHECK(s.check() == SolverResult::UNSAT);
}

TEST_CASE("bitwuzla.model after an equality of narrow arrays") {
  // -- Bitwuzla moves q = (a = b) into q's definition, and then gives q the
  // -- value "a's and b's value terms are the same", which is wrong when
  // -- every index is written (review of step 1.6, probes p1, p2, p5). So
  // -- while an assertion has an array equality with indices narrower than
  // -- 32 bits, the model has no values at all.
  Env env;
  using namespace op::array;
  bitwuzla_solver_impl bzla;
  Solver &s = bzla;
  Expr q = env.boolc("q"), p = env.boolc("p"), x = env.bvc("x", 8);
  Expr c3 = constArray(env.bvsort(2), env.num(3, 8));
  Expr c7 = constArray(env.bvsort(2), env.num(7, 8));
  Expr all7 = c3;
  for (unsigned n = 0; n < 4; ++n)
    all7 = store(all7, env.num(n, 2), env.num(7, 8));
  auto noValues = [&](Solver::model_ref m) {
    for (Expr e : {q, p, x, mk<NEG>(q), env.num(1, 8)}) {
      INFO(*e);
      CHECK(isOpX<NONDET>(m->eval(e, true)));
    }
    // -- a struct is still a struct, of nondets
    Expr st = m->eval(strct::mk(q, x), false);
    REQUIRE(isOpX<MK_STRUCT>(st));
    CHECK(isOpX<NONDET>(st->arg(0)));
    CHECK(isOpX<NONDET>(st->arg(1)));
  };

  // -- p5: q must be true; Bitwuzla's value of q is false
  CHECK(s.add(mk<EQ>(q, mk<EQ>(all7, c7))));
  CHECK(s.add(mk<EQ>(x, env.num(1, 8))));
  REQUIRE(s.check() == SolverResult::SAT);
  noValues(s.get_model());

  // -- p1, p2: 1-bit indices, a is 5 at both, so a = const(5); Bitwuzla
  // -- gives p false, x 0 and m d's value
  s.reset();
  Expr a = env.arrc("a", 1, 8), c5 = constArray(env.bvsort(1), env.num(5, 8));
  Expr c = env.arrc("c", 1, 8), d = env.arrc("d", 1, 8);
  Expr m = env.arrc("m", 1, 8);
  CHECK(s.add(mk<EQ>(select(a, env.num(0, 1)), env.num(5, 8))));
  CHECK(s.add(mk<EQ>(select(a, env.num(1, 1)), env.num(5, 8))));
  CHECK(s.add(mk<EQ>(p, mk<EQ>(a, c5))));
  CHECK(s.add(mk<EQ>(m, mk<ITE>(mk<EQ>(a, c5), c, d))));
  CHECK(s.add(mk<EQ>(select(c, env.num(0, 1)), env.num(1, 8))));
  CHECK(s.add(mk<EQ>(select(d, env.num(0, 1)), env.num(2, 8))));
  CHECK(s.add(mk<EQ>(x, mk<ITE>(mk<NEQ>(a, c5), env.num(0, 8), env.num(1, 8)))));
  REQUIRE(s.check() == SolverResult::SAT);
  Solver::model_ref mm = s.get_model();
  noValues(mm);
  CHECK(isOpX<NONDET>(mm->eval(m, true)));
  CHECK(isOpX<NONDET>(mm->eval(select(m, env.num(0, 1)), true)));

  // -- with 64-bit indices, as SeaHorn's memory has, values are given and
  // -- right: q is forced true through its definition
  s.reset();
  Expr a64 = env.arrc("a64", 64, 8), b64 = env.arrc("b64", 64, 8);
  Expr i = env.bvc("i", 64);
  CHECK(s.add(mk<EQ>(q, mk<EQ>(a64, b64))));
  CHECK(s.add(mk<EQ>(a64, store(b64, i, select(b64, i)))));
  CHECK(s.add(mk<EQ>(x, env.num(1, 8))));
  REQUIRE(s.check() == SolverResult::SAT);
  Solver::model_ref m64 = s.get_model();
  CHECK(m64->eval(q, true) == mk<TRUE>(env.efac));
  CHECK(m64->eval(x, true) == env.num(1, 8));
  // -- the equality itself is still not evaluated (the term guard)
  CHECK(isOpX<NONDET>(m64->eval(mk<EQ>(a64, b64), true)));

  // -- one narrow equality among wide ones is enough, and a disequality too
  CHECK(s.add(mk<NEQ>(all7, c3)));
  REQUIRE(s.check() == SolverResult::SAT);
  CHECK(isOpX<NONDET>(s.get_model()->eval(x, true)));
  // -- and reset() ends it
  s.reset();
  CHECK(s.add(mk<EQ>(x, env.num(2, 8))));
  REQUIRE(s.check() == SolverResult::SAT);
  CHECK(s.get_model()->eval(x, true) == env.num(2, 8));
  // -- an array equality with a narrow index in a term only, not in an
  // -- assertion, refuses only that term
  CHECK(isOpX<NONDET>(s.get_model()->eval(mk<EQ>(all7, c7), true)));
  CHECK(s.get_model()->eval(x, true) == env.num(2, 8));

  // -- the boundary: 31-bit indices are narrow, 32-bit ones are not
  for (unsigned iw : {8u, 31u, 32u}) {
    INFO("index width " << iw);
    s.reset();
    Expr aw = env.arrc("aw" + std::to_string(iw), iw, 8);
    Expr bw = env.arrc("bw" + std::to_string(iw), iw, 8);
    CHECK(s.add(mk<EQ>(q, mk<NEQ>(aw, bw))));
    CHECK(s.add(mk<EQ>(x, env.num(3, 8))));
    REQUIRE(s.check() == SolverResult::SAT);
    Expr vx = s.get_model()->eval(x, true);
    if (iw < 32)
      CHECK(isOpX<NONDET>(vx));
    else
      CHECK(vx == env.num(3, 8));
  }
}

TEST_CASE("bitwuzla.model print with arrays") {
  Env env;
  bitwuzla_solver_impl bzla;
  Solver &s = bzla;
  Expr a = env.arrc("a", 2, 8), x = env.bvc("x", 8);
  auto str = [](Expr e) { return boost::lexical_cast<std::string>(*e); };
  CHECK(s.add(mk<EQ>(op::array::select(a, env.num(1, 2)), x)));
  CHECK(s.add(mk<EQ>(x, env.num(4, 8))));
  REQUIRE(s.check() == SolverResult::SAT);
  Solver::model_ref m = s.get_model();
  std::string out;
  llvm::raw_string_ostream os(out);
  m->print(os);
  CHECK(os.str() == "a = " + str(m->eval(a, true)) + "\nx = " +
                        str(env.num(4, 8)) + "\n");
  CHECK(os.str().find("store(") != std::string::npos);
}

TEST_CASE("bitwuzla.model of structs") {
  // -- with --horn-bv2-extra-widemem, SeaHorn asks the model for registers
  // -- that are structs of terms (pointers, memories); like Z3's model, each
  // -- field is evaluated
  Env env;
  bitwuzla_solver_impl bzla;
  Solver &s = bzla;
  Expr x = env.bvc("x", 8), a = env.arrc("a", 64, 8);
  Expr i = bind::intConst(mkTerm<std::string>("i", env.efac));
  CHECK(s.add(mk<EQ>(x, env.num(3, 8))));
  CHECK(s.add(mk<EQ>(op::array::select(a, env.num(0, 64)), env.num(9, 8))));
  REQUIRE(s.check() == SolverResult::SAT);
  Solver::model_ref m = s.get_model();

  Expr v = m->eval(strct::mk(x, mk<BADD>(x, env.num(1, 8))), false);
  CHECK(v == strct::mk(env.num(3, 8), env.num(4, 8)));
  // -- fields of any kind, nested structs, and fields it cannot evaluate
  Expr va = m->eval(a, true);
  REQUIRE(isOpX<STORE>(va));
  CHECK(m->eval(strct::mk(a, x), true) == strct::mk(va, env.num(3, 8)));
  CHECK(m->eval(strct::mk(strct::mk(x), x), true) ==
        strct::mk(strct::mk(env.num(3, 8)), env.num(3, 8)));
  Expr vi = m->eval(strct::mk(i, x), true);
  REQUIRE(isOpX<MK_STRUCT>(vi));
  CHECK(isOpX<NONDET>(vi->arg(0)));
  CHECK(vi->arg(1) == env.num(3, 8));
  // -- an array equality inside a field is refused there
  Expr ve = m->eval(strct::mk(mk<EQ>(a, a), x), true);
  REQUIRE(isOpX<MK_STRUCT>(ve));
  CHECK(isOpX<NONDET>(ve->arg(0)));
  // -- an out-of-date model has no values, not even a struct of them
  CHECK(s.add(mk<EQ>(x, x)));
  CHECK(isOpX<NONDET>(m->eval(strct::mk(x, x), false)));
}

TEST_CASE("bitwuzla.encoding check with arrays") {
  Env env;
  using namespace op::array;
  auto verdict = [&](Expr e, const bz::Term &t) {
    auto ec = checkBitwuzlaEncoding(e, t, 10000);
    INFO(verdictName(ec.verdict) << ": " << ec.detail);
    return ec.verdict;
  };
  Expr a = env.arrc("a", 64, 8), b = env.arrc("b", 64, 8);
  Expr i = env.bvc("i", 64), j = env.bvc("j", 64), v = env.bvc("v", 8);
  Expr c = constArray(env.bvsort(64), v);
  for (Expr e : {mk<EQ>(select(store(a, i, v), j), v),
                 mk<EQ>(a, store(b, i, select(c, j))),
                 mk<NEQ>(mk<ITE>(mk<EQ>(i, j), a, b), c)}) {
    INFO(*e);
    CHECK(verdict(e, env.m.encode_term(e)) == EncodingVerdict::SAME);
  }
  // -- a wrong encoding is found: read over write at another index
  Expr e = mk<EQ>(select(store(a, i, v), j), v);
  Expr wrong = mk<EQ>(select(a, j), v);
  CHECK(verdict(e, env.m.encode_term(wrong)) == EncodingVerdict::DIFFERENT);
  // -- and a constant array of another value
  Expr e2 = mk<EQ>(select(c, j), v);
  Expr wrong2 = mk<EQ>(select(constArray(env.bvsort(64), env.num(0, 8)), j), v);
  CHECK(verdict(e2, env.m.encode_term(wrong2)) == EncodingVerdict::DIFFERENT);
}


TEST_CASE("bitwuzla.lambdas") {
  // -- plan 1.7: lambdas are Bitwuzla functions; fapp, select and store on
  // -- them; scoping of bound variables
  Env env;
  using namespace op::array;
  Expr p = env.bvc("p", 8), q = env.bvc("q", 8), v = env.bvc("v", 8);
  Expr i = env.bvc("i", 8), j = env.bvc("j", 8);
  Expr A = env.arrc("A", 8, 8);
  Expr x0 = env.bvar(0, 8);
  Expr inc = env.lam("x", 8, mk<BADD>(x0, env.num(1, 8)));
  // -- L1: application
  CHECK(env.valid(mk<EQ>(mk<FAPP>(inc, env.num(3, 8)), env.num(4, 8))));
  Expr mem = env.lam("addr", 8,
                     mk<ITE>(mk<EQ>(x0, p), v, select(A, x0)));
  CHECK(env.valid(mk<EQ>(mk<FAPP>(mem, p), v)));
  CHECK(env.valid(mk<IMPL>(mk<NEQ>(q, p),
                           mk<EQ>(mk<FAPP>(mem, q), select(A, q)))));
  CHECK_FALSE(env.valid(mk<EQ>(mk<FAPP>(mem, q), select(A, q))));
  // -- select and store on a lambda behave as on an array
  CHECK(env.valid(mk<EQ>(select(mem, i), mk<FAPP>(mem, i))));
  Expr st = store(mem, i, env.num(9, 8));
  CHECK(env.valid(mk<EQ>(select(st, i), env.num(9, 8))));
  CHECK(env.valid(mk<IMPL>(mk<NEQ>(i, j),
                           mk<EQ>(select(st, j), mk<FAPP>(mem, j)))));

  // -- L2: the same open body under two lambdas means each one's variable
  Expr body = mk<BADD>(x0, env.num(1, 8));
  Expr la = env.lam("a", 8, body), lb = env.lam("b", 8, body);
  CHECK(env.valid(mk<AND>(mk<EQ>(mk<FAPP>(la, env.num(3, 8)), env.num(4, 8)),
                          mk<EQ>(mk<FAPP>(lb, env.num(10, 8)),
                                 env.num(11, 8)))));
  // -- bvar(1) under a nested binder is the outer variable:
  // -- (lambda x. (lambda y. x - y)(1))(5) = 4
  Expr inner = env.lam("y", 8, mk<BSUB>(env.bvar(1, 8), env.bvar(0, 8)));
  Expr outer = env.lam("x", 8, mk<FAPP>(inner, env.num(1, 8)));
  CHECK(env.valid(mk<EQ>(mk<FAPP>(outer, env.num(5, 8)), env.num(4, 8))));
  // -- two variables: index 0 is the last one, as in Z3, and the arguments
  // -- of an application keep their order: (lambda a b. a - b)(5, 1) = 4
  Expr sub2 = mk<LAMBDA>(env.bdecl("a", 8), env.bdecl("b", 8),
                         mk<BSUB>(env.bvar(1, 8), env.bvar(0, 8)));
  CHECK(env.valid(mk<EQ>(mk<FAPP>(sub2, env.num(5, 8), env.num(1, 8)),
                         env.num(4, 8))));
  // -- one inner lambda that uses the enclosing variable, under two
  // -- different enclosing lambdas: each must see its own variable
  Expr usesOuter = env.lam("y", 8, env.bvar(1, 8));
  Expr outerA = env.lam("a", 8, mk<BADD>(mk<FAPP>(usesOuter, env.num(0, 8)),
                                         env.num(1, 8)));
  Expr outerB = env.lam("b", 8, mk<BADD>(mk<FAPP>(usesOuter, env.num(0, 8)),
                                         env.num(2, 8)));
  CHECK(env.valid(mk<AND>(mk<EQ>(mk<FAPP>(outerA, env.num(3, 8)), env.num(4, 8)),
                          mk<EQ>(mk<FAPP>(outerB, env.num(10, 8)),
                                 env.num(12, 8)))));
  // -- a bound variable outside its binder, or of another sort, is rejected
  Expr b0 = env.bvar(0, 8);
  CHECK(env.rejects(mk<EQ>(b0, p), b0));
  Expr wrongSort = env.bvar(0, 4);
  Expr lw = env.lam("w", 8, mk<EQ>(wrongSort, env.num(0, 4)));
  CHECK(env.rejects(mk<FAPP>(lw, p), wrongSort));
  // -- and the encoder still works after a rejection inside a binder: its
  // -- scope is gone, so a free bvar is still rejected
  CHECK(env.valid(mk<EQ>(mk<FAPP>(inc, env.num(7, 8)), env.num(8, 8))));
  CHECK(env.rejects(mk<EQ>(b0, q), b0));

  // -- L5: rejected shapes, naming the culprit
  Expr nested = env.lam("u", 8, env.lam("w", 8, env.bvar(1, 8)));
  CHECK(env.rejects(mk<EQ>(mk<FAPP>(mk<FAPP>(nested, p), q), p), nested));
  Expr adecl = bind::fname(
      bind::mkConst(mkTerm<std::string>("m", env.efac),
                    sort::arrayTy(env.bvsort(8), env.bvsort(8))));
  Expr overArray = mk<LAMBDA>(adecl, select(bind::bvar(0, sort::arrayTy(
                                                     env.bvsort(8),
                                                     env.bvsort(8))),
                                            p));
  CHECK(env.rejects(mk<EQ>(mk<FAPP>(overArray, A), p), overArray));
  Expr f = bind::fdecl(mkTerm<std::string>("f", env.efac),
                       ExprVector{env.bvsort(8), env.bvsort(8)});
  Expr fp = bind::fapp(f, p);
  CHECK(env.rejects(mk<EQ>(fp, p), fp));
  // -- C1: the other rejections of 1.7, each naming its culprit
  {
    // -- a bound variable of a sort Bitwuzla lacks, under a bit-vector binder
    Expr intVar = bind::bvar(0, sort::intTy(env.efac));
    CHECK(env.rejects(mk<EQ>(mk<FAPP>(env.lam("x", 8, intVar), p), p),
                      intVar));
    // -- a binder over a variable of such a sort
    Expr ndecl = bind::fname(bind::mkConst(mkTerm<std::string>("n", env.efac),
                                           sort::intTy(env.efac)));
    Expr overInt = mk<FORALL>(ndecl, mk<TRUE>(env.efac));
    CHECK(env.rejects(overInt, overInt));
    // -- a forall whose body is not a formula: Bitwuzla rejects it
    Expr bvBody = mk<FORALL>(env.bdecl("z", 8), env.bvar(0, 8));
    CHECK(env.rejects(mk<EQ>(mk<ITE>(bvBody, p, q), p), bvBody));
    // -- ite and store with two arguments
    Expr ite2 = mknary<ITE>(ExprVector{env.boolc("c"), p});
    CHECK(env.rejects(mk<EQ>(ite2, p), ite2));
    Expr store2 = mknary<STORE>(ExprVector{A, p});
    CHECK(env.rejects(mk<EQ>(select(store2, p), p), store2));
    // -- the application of a bit-vector
    Expr appBv = mk<FAPP>(p, q);
    CHECK(env.rejects(mk<EQ>(appBv, p), appBv));
    // -- a store into a function of two arguments
    Expr two = mk<LAMBDA>(env.bdecl("a", 8), env.bdecl("b", 8), env.bvar(1, 8));
    Expr storeTwo = store(two, p, q);
    CHECK(env.rejects(mk<EQ>(mk<FAPP>(storeTwo, p, q), p), storeTwo));
    // -- a leaf that is no constant, numeral or bound variable
    Expr num = mkTerm<expr::mpz_class>(expr::mpz_class(5ul), env.efac);
    CHECK(env.rejects(num, num));
  }
  // -- and the solver answers unknown on each, then correctly after reset
  bitwuzla_solver_impl bzla;
  Solver &s = bzla;
  for (Expr bad : {mk<EQ>(mk<FAPP>(mk<FAPP>(nested, p), q), p),
                   mk<EQ>(mk<FAPP>(overArray, A), p), mk<EQ>(fp, p)}) {
    INFO(*bad);
    CHECK(s.add(mk<NEQ>(mk<FAPP>(inc, p), mk<BADD>(p, env.num(1, 8)))));
    CHECK_FALSE(s.add(bad));
    CHECK(s.check() == SolverResult::UNKNOWN);
    s.reset();
    CHECK(s.add(mk<NEQ>(mk<FAPP>(inc, p), mk<BADD>(p, env.num(1, 8)))));
    CHECK(s.check() == SolverResult::UNSAT);
    s.reset();
  }
}

TEST_CASE("bitwuzla.equality and ite with functions") {
  // -- L3: equality with a function is pointwise; ite over functions
  Env env;
  using namespace op::array;
  const SolverResult SAT = SolverResult::SAT, UNSAT = SolverResult::UNSAT;
  Expr p = env.bvc("p", 8), c = env.boolc("c");
  Expr A = env.arrc("A", 8, 8), B = env.arrc("B", 8, 8);
  Expr x0 = env.bvar(0, 8);
  Expr lamB = env.lam("addr", 8, mk<ITE>(mk<EQ>(x0, p), env.num(7, 8),
                                         select(B, x0)));
  // -- array = lambda, as a memory PHI asserts it
  CHECK(adapterCheck({mk<EQ>(A, lamB)}) == SAT);
  CHECK(adapterCheck({mk<EQ>(A, lamB),
                      mk<NEQ>(select(A, p), env.num(7, 8))}) == UNSAT);
  CHECK(adapterCheck({mk<IMPL>(c, mk<EQ>(A, lamB)),
                      mk<NEQ>(select(A, p), env.num(7, 8))}) == SAT);
  CHECK(adapterCheck({mk<IMPL>(c, mk<EQ>(A, lamB)), c,
                      mk<NEQ>(select(A, p), env.num(7, 8))}) == UNSAT);
  // -- lambda = lambda, and !=
  Expr l1 = env.lam("x", 8, mk<BADD>(x0, env.num(1, 8)));
  Expr l1b = env.lam("y", 8, mk<BADD>(env.num(1, 8), x0));
  Expr l2 = env.lam("z", 8, mk<BADD>(x0, env.num(2, 8)));
  CHECK(adapterCheck({mk<NEQ>(l1, l1b)}) == UNSAT);
  CHECK(adapterCheck({mk<NEQ>(l1, l2)}) == SAT);
  CHECK(adapterCheck({mk<EQ>(l1, l2)}) == UNSAT);
  // -- ite over lambdas: no crash, and the right answer
  Expr it = mk<ITE>(c, l1, l2);
  CHECK(adapterCheck({c, mk<NEQ>(mk<FAPP>(it, env.num(3, 8)),
                                 env.num(4, 8))}) == UNSAT);
  CHECK(adapterCheck({mk<NEG>(c), mk<EQ>(select(it, env.num(3, 8)),
                                         env.num(5, 8))}) == SAT);
  // -- ite of an array and a lambda
  Expr mixed = mk<ITE>(c, A, l1);
  CHECK(adapterCheck({mk<NEG>(c), mk<NEQ>(mk<FAPP>(mixed, p),
                                          mk<BADD>(p, env.num(1, 8)))}) ==
        UNSAT);
}

TEST_CASE("bitwuzla.time limit") {
  // -- factoring a 40-bit number takes Bitwuzla about 2 s (probe17g); with a
  // -- 50 ms limit the check runs out and answers unknown
  Env env;
  Expr x = env.bvc("fx", 40), y = env.bvc("fy", 40);
  Expr n = bv::bvnum(expr::mpz_class("1099503239183"), 40, env.efac);
  ExprVector f{mk<EQ>(mk<BMUL>(x, y), n), mk<BUGT>(x, env.num(1, 40)),
               mk<BUGT>(y, env.num(1, 40)), mk<UMUL_NO_OVERFLOW>(x, y)};
  bitwuzla_solver_impl limited(50);
  for (Expr e : f)
    CHECK(limited.add(e));
  CHECK(limited.check() == SolverResult::UNKNOWN);
  // -- without a limit it is sat
  bitwuzla_solver_impl unlimited;
  for (Expr e : f)
    CHECK(unlimited.add(e));
  CHECK(unlimited.check() == SolverResult::SAT);
}

TEST_CASE("bitwuzla.quantifiers") {
  // -- L4: small forall and exists formulas over bit-vectors
  Env env;
  const SolverResult SAT = SolverResult::SAT, UNSAT = SolverResult::UNSAT;
  Expr x0 = env.bvar(0, 4), y = env.bvc("y4", 4);
  auto all = [&](Expr body) { return mk<FORALL>(env.bdecl("x", 4), body); };
  auto some = [&](Expr body) { return mk<EXISTS>(env.bdecl("x", 4), body); };
  CHECK(adapterCheck({mk<NEG>(all(mk<EQ>(mk<BADD>(x0, env.num(0, 4)), x0)))}) ==
        UNSAT);
  CHECK(adapterCheck({mk<NEG>(some(mk<EQ>(mk<BADD>(x0, env.num(1, 4)),
                                          env.num(0, 4))))}) == UNSAT);
  CHECK(adapterCheck({all(mk<EQ>(x0, y))}) == UNSAT);
  // -- squares mod 16 are 0, 1, 4 and 9
  CHECK(adapterCheck({some(mk<EQ>(mk<BMUL>(x0, x0), env.num(2, 4)))}) ==
        UNSAT);
  CHECK(adapterCheck({some(mk<EQ>(mk<BMUL>(x0, x0), y))}) == SAT);
  // -- Bool bound variables
  auto allB = [&](Expr body) {
    return mk<FORALL>(bind::fname(env.boolc("b")), body);
  };
  Expr b0 = bind::bvar(0, sort::boolTy(env.efac));
  CHECK(adapterCheck({mk<NEG>(allB(mk<OR>(b0, mk<NEG>(b0))))}) == UNSAT);
  CHECK(adapterCheck({allB(mk<OR>(b0, env.boolc("pb")))}) == SAT);
  CHECK(adapterCheck({allB(mk<OR>(b0, env.boolc("pb"))),
                      mk<NEG>(env.boolc("pb"))}) == UNSAT);
  // -- forall y' . y' <= y (unsigned) forces y = 15
  CHECK(adapterCheck({all(mk<BULE>(x0, y)), mk<NEQ>(y, env.num(15, 4))}) ==
        UNSAT);
}

TEST_CASE("bitwuzla.model with lambdas and quantifiers") {
  Env env;
  EZ3 z3(env.efac);
  using namespace op::array;
  Expr p = env.bvc("p", 8), x = env.bvc("x", 8), A = env.arrc("A", 8, 8);
  Expr x0 = env.bvar(0, 8);
  Expr mem = env.lam("addr", 8,
                     mk<ITE>(mk<EQ>(x0, p), env.num(7, 8), select(A, x0)));
  bitwuzla_solver_impl bzla;
  Solver &s = bzla;
  CHECK(s.add(mk<EQ>(mk<FAPP>(mem, x), env.num(3, 8))));
  REQUIRE(s.check() == SolverResult::SAT);
  Solver::model_ref m = s.get_model();
  // -- M1: a function has no value; an application has, and Z3 agrees
  CHECK(isOpX<NONDET>(m->eval(mem, true)));
  CHECK(isOpX<NONDET>(m->eval(mk<ITE>(env.boolc("c"), mem, mem), true)));
  Expr vx = m->eval(x, true), vp = m->eval(p, true), vA = m->eval(A, true);
  REQUIRE(isUnsignedBvNum(vx));
  CHECK(m->eval(mk<FAPP>(mem, x), true) == env.num(3, 8));
  Expr app = mk<FAPP>(mem, mk<BADD>(x, env.num(1, 8)));
  Expr vapp = m->eval(app, false);
  REQUIRE(isUnsignedBvNum(vapp));
  CHECK(z3Valid(z3, mk<IMPL>(mk<AND>(mk<EQ>(x, vx), mk<EQ>(p, vp),
                                     mk<EQ>(A, vA)),
                             mk<EQ>(app, vapp))));
  // -- M2: a term with a quantifier inside has no value
  Expr all = mk<FORALL>(env.bdecl("y", 8), mk<EQ>(env.bvar(0, 8), x));
  CHECK(isOpX<NONDET>(m->eval(all, true)));
  CHECK(isOpX<NONDET>(m->eval(mk<EQ>(A, mem), true)));
  // -- also below the top of the term
  CHECK(isOpX<NONDET>(m->eval(mk<AND>(mk<EQ>(x, x), all), true)));
  CHECK(isOpX<NONDET>(m->eval(mk<ITE>(mk<EQ>(A, mem), x, p), true)));
  CHECK(m->eval(x, false) == vx);
  // -- while an assertion has a quantifier (here from an equality with a
  // -- function), no term has a value
  CHECK(s.add(mk<EQ>(A, mem)));
  REQUIRE(s.check() == SolverResult::SAT);
  Solver::model_ref mq = s.get_model();
  for (Expr t : {x, p, mk<FAPP>(mem, x), mk<EQ>(x, x)}) {
    INFO(*t);
    CHECK(isOpX<NONDET>(mq->eval(t, true)));
  }
  Expr st = mq->eval(strct::mk(x, p), true);
  REQUIRE(isOpX<MK_STRUCT>(st));
  CHECK(isOpX<NONDET>(st->arg(0)));
  // -- and after reset, values come back
  s.reset();
  CHECK(s.add(mk<EQ>(x, env.num(5, 8))));
  REQUIRE(s.check() == SolverResult::SAT);
  CHECK(s.get_model()->eval(x, true) == env.num(5, 8));
  // -- a forall written in SeaHorn sets the guard too
  CHECK(s.add(mk<FORALL>(env.bdecl("y", 8),
                         mk<EQ>(mk<BAND>(env.bvar(0, 8), env.num(0, 8)),
                                env.num(0, 8)))));
  REQUIRE(s.check() == SolverResult::SAT);
  CHECK(isOpX<NONDET>(s.get_model()->eval(x, true)));
}

TEST_CASE("bitwuzla.encoding check with lambdas") {
  // -- F1: terms with binders, printed with lets at the top (Bitwuzla's own
  // -- printer gets let scopes wrong under binders)
  Env env;
  using namespace op::array;
  auto verdict = [&](Expr e, const bz::Term &t, bz::TermManager *tm) {
    auto ec = checkBitwuzlaEncoding(e, t, 10000, tm);
    INFO(verdictName(ec.verdict) << ": " << ec.detail);
    return ec.verdict;
  };
  Expr p = env.bvc("p", 8), q = env.bvc("q", 8), c = env.boolc("c");
  Expr A = env.arrc("A", 8, 8), B = env.arrc("B", 8, 8);
  Expr x0 = env.bvar(0, 8);
  Expr mem = env.lam("addr", 8,
                     mk<ITE>(mk<EQ>(x0, p), env.num(7, 8), select(A, x0)));
  // -- shared inside and outside binders, as in probe17d
  Expr s1 = mk<BADD>(p, q), s2 = mk<BADD>(s1, s1);
  Expr inner = env.lam("y", 8, mk<ITE>(mk<EQ>(x0, s2), mk<BADD>(s2, s2),
                                       select(A, mk<BADD>(x0, s1))));
  Expr outer = env.lam("x", 8, mk<ITE>(mk<EQ>(x0, s2),
                                       mk<FAPP>(inner, s1),
                                       mk<FAPP>(inner, mk<BADD>(x0, s1))));
  Expr all = mk<FORALL>(env.bdecl("z", 8),
                        mk<BULE>(mk<BAND>(env.bvar(0, 8), p), p));
  for (Expr e : {mk<EQ>(mk<FAPP>(mem, q), env.num(3, 8)),
                 mk<EQ>(select(store(mem, q, p), p), q),
                 mk<IMPL>(c, mk<EQ>(B, mem)), mk<NEQ>(B, mem),
                 mk<EQ>(mk<FAPP>(mk<ITE>(c, mem, B), q), p),
                 mk<AND>(mk<EQ>(mk<FAPP>(outer, s2), s1),
                         mk<EQ>(mk<FAPP>(inner, s1), s2)),
                 all}) {
    INFO(*e);
    CHECK(verdict(e, env.m.encode_term(e), &env.tm) == EncodingVerdict::SAME);
  }
  // -- a wrong encoding is found
  Expr e = mk<EQ>(mk<FAPP>(mem, q), env.num(3, 8));
  Expr mem2 = env.lam("addr", 8,
                      mk<ITE>(mk<EQ>(x0, q), env.num(7, 8), select(A, x0)));
  Expr wrong = mk<EQ>(mk<FAPP>(mem2, q), env.num(3, 8));
  CHECK(verdict(e, env.m.encode_term(wrong), &env.tm) ==
        EncodingVerdict::DIFFERENT);
  Expr wrongAll = mk<FORALL>(env.bdecl("z", 8),
                             mk<BULT>(mk<BAND>(env.bvar(0, 8), p), p));
  // -- with a quantifier, Z3's sat is not trusted (it has answered sat
  // -- wrongly on equal formulas with lambdas): the wrong encoding is
  // -- UNDECIDED, never SAME (criterion F1 asked for DIFFERENT here)
  CHECK(verdict(all, env.m.encode_term(wrongAll), &env.tm) ==
        EncodingVerdict::UNDECIDED);
  // -- without the TermManager, a term with binders is not checked
  CHECK(verdict(e, env.m.encode_term(e), nullptr) ==
        EncodingVerdict::UNCHECKED);
  // -- nested binders with the same name, the inner one using the outer
  // -- variable: printed names must keep them apart
  Expr nestedSame = env.lam("v", 8, mk<BADD>(mk<FAPP>(env.lam("v", 8,
                                             mk<BADD>(env.bvar(1, 8),
                                                      env.bvar(0, 8))),
                                             env.num(1, 8)),
                                             env.bvar(0, 8)));
  Expr eNested = mk<EQ>(mk<FAPP>(nestedSame, q), p);
  CHECK(verdict(eNested, env.m.encode_term(eNested), &env.tm) ==
        EncodingVerdict::SAME);
  // -- an open subterm shared inside and outside a nested binder
  Expr shared = mk<BADD>(x0, env.num(1, 8));
  Expr sharedIn = env.lam("y", 8, mk<BADD>(mk<BADD>(env.bvar(1, 8), env.num(1, 8)),
                                           env.bvar(0, 8)));
  Expr sharedOut = env.lam("x", 8, mk<ITE>(mk<EQ>(shared, p),
                                           mk<FAPP>(sharedIn, shared), shared));
  Expr eShared = mk<EQ>(mk<FAPP>(sharedOut, q), p);
  CHECK(verdict(eShared, env.m.encode_term(eShared), &env.tm) ==
        EncodingVerdict::SAME);
  // -- a binder of two variables
  Expr all2 = mk<FORALL>(env.bdecl("a", 8), env.bdecl("b", 8),
                         mk<BULE>(mk<BAND>(env.bvar(1, 8), env.bvar(0, 8)),
                                  env.bvar(1, 8)));
  CHECK(verdict(all2, env.m.encode_term(all2), &env.tm) ==
        EncodingVerdict::SAME);
  // -- a wrong pointwise encoding prints with no quantifier (= B mem2), so
  // -- Z3 can show values; with a quantifier in the term, it stays UNDECIDED
  Expr eB = mk<EQ>(B, mem);
  CHECK(verdict(eB, env.m.encode_term(mk<EQ>(B, mem2)), &env.tm) ==
        EncodingVerdict::UNDECIDED);

  // -- only an encoder's pointwise equality is printed as an equality: not
  // -- an exists, and not with the variables in another order (either would
  // -- make SAME of two different formulas)
  {
    bz::Sort b8 = env.tm.mk_bv_sort(8);
    bz::Term a = env.m.encode_term(A), b = env.m.encode_term(B);
    bz::Term xv = env.tm.mk_var(b8, "ex!1");
    bz::Term ex = env.tm.mk_term(
        bz::Kind::EXISTS,
        {xv, env.tm.mk_term(bz::Kind::EQUAL,
                            {env.tm.mk_term(bz::Kind::ARRAY_SELECT, {a, xv}),
                             env.tm.mk_term(bz::Kind::ARRAY_SELECT, {b, xv})})});
    CHECK(verdict(mk<EQ>(A, B), ex, &env.tm) != EncodingVerdict::SAME);
    // -- f = g = (lambda a b. a): forall x y. f(x, y) = g(y, x) is false,
    // -- f = g is true
    Expr first = mk<LAMBDA>(env.bdecl("a", 8), env.bdecl("b", 8),
                            env.bvar(1, 8));
    bz::Term f2 = env.m.encode_term(first);
    bz::Term u = env.tm.mk_var(b8, "u!1"), w = env.tm.mk_var(b8, "w!1");
    bz::Term swapped = env.tm.mk_term(
        bz::Kind::FORALL,
        {u, w, env.tm.mk_term(bz::Kind::EQUAL,
                              {env.tm.mk_term(bz::Kind::APPLY, {f2, u, w}),
                               env.tm.mk_term(bz::Kind::APPLY, {f2, w, u})})});
    CHECK(verdict(mk<EQ>(first, first), swapped, &env.tm) !=
          EncodingVerdict::SAME);
  }
  // -- two bound variables of one name are not checked (printed, they could
  // -- be read as one): forall x. exists x. x + p = x + 1
  {
    bz::Sort b8 = env.tm.mk_bv_sort(8);
    bz::Term v1 = env.tm.mk_var(b8, "x"), v2 = env.tm.mk_var(b8, "x");
    bz::Term tp = env.m.encode_term(p);
    bz::Term dup = env.tm.mk_term(
        bz::Kind::FORALL,
        {v1, env.tm.mk_term(
                 bz::Kind::EXISTS,
                 {v2, env.tm.mk_term(
                          bz::Kind::EQUAL,
                          {env.tm.mk_term(bz::Kind::BV_ADD, {v1, tp}),
                           env.tm.mk_term(bz::Kind::BV_ADD,
                                          {v2, env.tm.mk_bv_one(b8)})})})});
    Expr eDup = mk<EQ>(p, env.num(1, 8));
    auto ec = checkBitwuzlaEncoding(eDup, dup, 10000, &env.tm);
    CHECK(ec.verdict == EncodingVerdict::UNCHECKED);
    CHECK(ec.detail.find("two variables") != std::string::npos);
  }
  // -- a forall whose sides are not applied to its variable is no pointwise
  // -- equality: forall x. A[p] = B[p] is not A = B
  {
    bz::Sort b8 = env.tm.mk_bv_sort(8);
    bz::Term a = env.m.encode_term(A), b = env.m.encode_term(B);
    bz::Term tp = env.m.encode_term(p), xv = env.tm.mk_var(b8, "xa!1");
    bz::Term atP = env.tm.mk_term(
        bz::Kind::FORALL,
        {xv, env.tm.mk_term(bz::Kind::EQUAL,
                            {env.tm.mk_term(bz::Kind::ARRAY_SELECT, {a, tp}),
                             env.tm.mk_term(bz::Kind::ARRAY_SELECT, {b, tp})})});
    CHECK(verdict(mk<EQ>(A, B), atP, &env.tm) != EncodingVerdict::SAME);
  }
  // -- a constant may not take the check's own let names
  Expr bwc = env.bvc("_bwc1", 8);
  Expr eBwc = mk<EQ>(mk<FAPP>(mem, bwc), p);
  {
    auto ec = checkBitwuzlaEncoding(eBwc, env.m.encode_term(eBwc), 10000,
                                    &env.tm);
    CHECK(ec.verdict == EncodingVerdict::UNCHECKED);
    CHECK(ec.detail.find("check's definitions") != std::string::npos);
  }
  // -- probe17i: open terms shared across nested lambdas inside one closed
  // -- lambda; Bitwuzla's lets get this wrong too, so definitions are
  // -- printed without them
  {
    Expr zc = env.bvc("zc", 8), yc = env.bvc("yc", 8), xc = env.bvc("xc", 8);
    Expr s1 = mk<BADD>(zc, q), s2 = mk<BADD>(s1, s1), s3 = mk<BMUL>(s2, s1);
    Expr in = bind::abs<LAMBDA>(ExprVector{yc},
                                mk<ITE>(mk<EQ>(yc, s3), mk<BADD>(s2, s2),
                                        select(A, mk<BADD>(yc, s1))));
    Expr out = bind::abs<LAMBDA>(
        ExprVector{xc},
        mk<ITE>(mk<EQ>(xc, s2),
                mk<BADD>(mk<FAPP>(in, s3), mk<BADD>(xc, xc)),
                mk<FAPP>(in, mk<BADD>(xc, s1))));
    Expr body = mk<AND>(mk<EQ>(mk<FAPP>(out, s2), mk<BADD>(s3, s3)),
                        mk<EQ>(mk<FAPP>(in, s1), s2));
    Expr wrap = bind::abs<LAMBDA>(ExprVector{zc},
                                  mk<ITE>(body, env.num(1, 8), env.num(0, 8)));
    REQUIRE(isOpX<LAMBDA>(wrap));
    Expr e17i = mk<EQ>(mk<FAPP>(wrap, q), env.num(1, 8));
    CHECK(verdict(e17i, env.m.encode_term(e17i), &env.tm) ==
          EncodingVerdict::SAME);
  }
  // -- fuzz formula 207 (seed 2): Z3 answered sat and evaluated its values
  // -- as a difference, though the two are the same formula. With an
  // -- equality between lambdas (a quantifier for Bitwuzla), that must not
  // -- become DIFFERENT.
  {
    Expr x3b = env.bvc("x3b", 3), x3a = env.bvc("x3a", 3);
    Expr x2b = env.bvc("x2b", 2), x13a = env.bvc("x13a", 13);
    Expr A23 = env.arrc("A2_3a", 2, 3);
    Expr p0 = env.boolc("p0"), p1 = env.boolc("p1");
    Expr b2 = env.bvar(0, 2);
    Expr C = constArray(env.bvsort(2), x3b);
    Expr L1 = env.lam("lx2", 2, select(C, b2));
    Expr L2 = env.lam("lx2", 2, select(A23, b2));
    Expr L3 = env.lam("lx2", 2, mk<ITE>(mk<EQ>(b2, x2b), x3a, mk<FAPP>(L2, b2)));
    Expr I = mk<ITE>(p1, mk<ITE>(p1, L1, L2), L3);
    Expr f207 = mk<NEG>(mknary<AND>(ExprVector{
        mk<BUGT>(mk<BNEG>(bv::zext(env.num(1, 1), 13)), x13a),
        mk<NEQ>(I, C), mk<NEG>(p0), mk<NEQ>(I, C)}));
    CHECK(verdict(f207, env.m.encode_term(f207), &env.tm) !=
          EncodingVerdict::DIFFERENT);
  }
  // -- a quantified formula whose difference Z3 can confirm (its rewriter
  // -- removes both quantifiers: forall z. z <= 255 is true, forall z.
  // -- z < 0 is false) is still UNDECIDED: with a quantifier, Z3's sat is
  // -- never taken as a difference, confirmed or not
  {
    Expr z = env.bvar(0, 8);
    Expr allTrue = mk<FORALL>(env.bdecl("z", 8), mk<BULE>(z, env.num(255, 8)));
    Expr allFalse = mk<FORALL>(env.bdecl("z", 8), mk<BULT>(z, env.num(0, 8)));
    CHECK(verdict(allTrue, env.m.encode_term(allTrue), &env.tm) ==
          EncodingVerdict::SAME);
    CHECK(verdict(allTrue, env.m.encode_term(allFalse), &env.tm) ==
          EncodingVerdict::UNDECIDED);
  }
  // -- C1: more shapes that are no pointwise equality, and variable names
  // -- the check refuses
  {
    bz::Sort b8 = env.tm.mk_bv_sort(8);
    bz::Term tp = env.m.encode_term(p);
    // -- f(p) = g(p) for every x is true; f = g is false
    Expr zeroAtP = env.lam("x", 8, mk<ITE>(mk<EQ>(x0, p), env.num(0, 8), x0));
    Expr zeroAtP1 = env.lam("x", 8, mk<ITE>(mk<EQ>(x0, p), env.num(0, 8),
                                            mk<BADD>(x0, env.num(1, 8))));
    bz::Term f1 = env.m.encode_term(zeroAtP), g1 = env.m.encode_term(zeroAtP1);
    bz::Term xv = env.tm.mk_var(b8, "xf!1");
    bz::Term atP = env.tm.mk_term(
        bz::Kind::FORALL,
        {xv, env.tm.mk_term(bz::Kind::EQUAL,
                            {env.tm.mk_term(bz::Kind::APPLY, {f1, tp}),
                             env.tm.mk_term(bz::Kind::APPLY, {g1, tp})})});
    CHECK(verdict(mk<EQ>(zeroAtP, zeroAtP1), atP, &env.tm) !=
          EncodingVerdict::SAME);
    // -- a side whose function uses the variable: forall x.
    // -- (lambda y. y + x)(x) = inc(x) is false; inc = inc is true
    Expr inc = env.lam("x", 8, mk<BADD>(x0, env.num(1, 8)));
    bz::Term yv = env.tm.mk_var(b8, "yo!1"), xo = env.tm.mk_var(b8, "xo!1");
    bz::Term open = env.tm.mk_term(
        bz::Kind::LAMBDA, {yv, env.tm.mk_term(bz::Kind::BV_ADD, {yv, xo})});
    bz::Term openSide = env.tm.mk_term(
        bz::Kind::FORALL,
        {xo, env.tm.mk_term(
                 bz::Kind::EQUAL,
                 {env.tm.mk_term(bz::Kind::APPLY, {open, xo}),
                  env.tm.mk_term(bz::Kind::APPLY,
                                 {env.m.encode_term(inc), xo})})});
    CHECK(verdict(mk<EQ>(inc, inc), openSide, &env.tm) !=
          EncodingVerdict::SAME);
    // -- a variable without a name, or with one of the check's names
    for (bz::Term v : {env.tm.mk_var(b8), env.tm.mk_var(b8, "_bwc7")}) {
      bz::Term t = env.tm.mk_term(
          bz::Kind::FORALL,
          {v, env.tm.mk_term(bz::Kind::EQUAL, {env.tm.mk_term(
                                                   bz::Kind::BV_AND, {v, tp}),
                                               env.tm.mk_term(
                                                   bz::Kind::BV_AND,
                                                   {tp, v})})});
      auto ec = checkBitwuzlaEncoding(mk<TRUE>(env.efac), t, 10000, &env.tm);
      INFO(ec.detail);
      CHECK(ec.verdict == EncodingVerdict::UNCHECKED);
      CHECK((ec.detail.find("has no name") != std::string::npos ||
             ec.detail.find("the name of variable _bwc7") != std::string::npos));
    }
  }
  // -- C1: SEAHORN_ENCODING_CHECK_DUMP writes the comparison of a sat
  // -- check to a file in the folder it names
  {
    std::string tmpl = std::string(std::getenv("TMPDIR") ? std::getenv("TMPDIR")
                                                         : "/tmp") +
                       "/bwdump.XXXXXX";
    std::vector<char> buf(tmpl.begin(), tmpl.end());
    buf.push_back('\0');
    REQUIRE(mkdtemp(buf.data()) != nullptr);
    std::string dir(buf.data());
    setenv("SEAHORN_ENCODING_CHECK_DUMP", dir.c_str(), 1);
    EncodingVerdict v = verdict(e, env.m.encode_term(wrong), &env.tm);
    unsetenv("SEAHORN_ENCODING_CHECK_DUMP");
    CHECK(v == EncodingVerdict::DIFFERENT);
    std::vector<std::string> files;
    if (DIR *d = opendir(dir.c_str())) {
      while (struct dirent *ent = readdir(d))
        if (std::string(ent->d_name).rfind("different-", 0) == 0)
          files.push_back(dir + "/" + ent->d_name);
      closedir(d);
    }
    REQUIRE(files.size() == 1);
    std::ifstream in(files[0]);
    std::string text((std::istreambuf_iterator<char>(in)),
                     std::istreambuf_iterator<char>());
    CHECK(text.find("; Z3's encoding:") != std::string::npos);
    CHECK(text.find("; values on which they differ:") != std::string::npos);
    std::remove(files[0].c_str());
    rmdir(dir.c_str());
  }
  // -- a free variable is reported as such
  {
    bz::Sort b8 = env.tm.mk_bv_sort(8);
    bz::Term fv = env.tm.mk_var(b8, "free!1"), bv = env.tm.mk_var(b8, "bnd!1");
    bz::Term lamFree = env.tm.mk_term(
        bz::Kind::LAMBDA, {bv, env.tm.mk_term(bz::Kind::BV_ADD, {bv, fv})});
    bz::Term t = env.tm.mk_term(
        bz::Kind::EQUAL, {env.tm.mk_term(bz::Kind::APPLY,
                                         {lamFree, env.m.encode_term(q)}),
                          env.m.encode_term(p)});
    auto ec = checkBitwuzlaEncoding(mk<EQ>(q, p), t, 10000, &env.tm);
    CHECK(ec.verdict == EncodingVerdict::UNCHECKED);
    CHECK(ec.detail.find("free variable") != std::string::npos);
  }
  // -- a term Z3 cannot parse: the message shows where
  {
    std::vector<seahorn::solver::SmtLibConst> consts{{"p", 8}};
    auto ec = checkSmtLibTermWithZ3(mk<EQ>(p, p), "(= p (no_such_function p))",
                                    consts, 0, 10000);
    CHECK(ec.verdict == EncodingVerdict::UNCHECKED);
    CHECK(ec.detail.find("near:") != std::string::npos);
  }

  // -- a bound variable named like a constant is not checked
  bz::Sort bv8 = env.tm.mk_bv_sort(8);
  bz::Term k = env.tm.mk_const(bv8, "k"), vk = env.tm.mk_var(bv8, "k");
  bz::Term clash = env.tm.mk_term(
      bz::Kind::FORALL, {vk, env.tm.mk_term(bz::Kind::BV_ULE, {vk, k})});
  Expr kc = env.bvc("k", 8);
  CHECK(verdict(mk<FORALL>(env.bdecl("v", 8), mk<BULE>(env.bvar(0, 8), kc)),
                clash, &env.tm) == EncodingVerdict::UNCHECKED);
}

#endif
