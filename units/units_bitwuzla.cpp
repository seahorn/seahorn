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

#include <cstdlib>
#include <fstream>
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
  if (bind::IsConst()(e) || bv::is_bvnum(e))
    return;
  if (isOpX<BEXTRACT>(e)) {
    termsOf(e->arg(2), seen, out);
    return;
  }
  if (isOpX<BSEXT>(e) || isOpX<BZEXT>(e)) {
    termsOf(e->arg(0), seen, out);
    return;
  }
  for (unsigned i = 0, sz = e->arity(); i < sz; ++i)
    termsOf(e->arg(i), seen, out);
}
} // namespace

TEST_CASE("bitwuzla.sorts") {
  Env env;
  CHECK(env.m.encode_sort(sort::boolTy(env.efac)).is_bool());
  CHECK(env.m.encode_sort(env.bvsort(13)).bv_size() == 13);
  CHECK_THROWS_AS(env.m.encode_sort(sort::intTy(env.efac)), UnsupportedExpr);
  CHECK_THROWS_AS(env.m.encode_sort(sort::realTy(env.efac)), UnsupportedExpr);
  // -- arrays come with memory (plan 1.6)
  CHECK_THROWS_AS(
      env.m.encode_sort(sort::arrayTy(env.bvsort(8), env.bvsort(8))),
      UnsupportedExpr);
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

  unsigned pick(unsigned n) {
    return std::uniform_int_distribution<unsigned>(0, n - 1)(m_rng);
  }
  bool chance(unsigned percent) { return pick(100) < percent; }
  unsigned width() {
    static const unsigned ws[] = {1, 2, 3, 4, 5, 8, 13, 16, 32, 64, 65, 128};
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
  Expr reused(unsigned w) {
    ExprVector &p = m_pool[w];
    return p.empty() || !chance(25) ? Expr() : p[pick(p.size())];
  }
  ExprVector bvArgs(unsigned n, unsigned w, unsigned depth) {
    ExprVector args;
    for (unsigned i = 0; i < n; ++i)
      args.push_back(bv(w, depth));
    return args;
  }

public:
  RandomFormulas(Env &env, unsigned seed) : m_env(env), m_rng(seed) {}

  /// A conjunction of up to four random atoms; small widths and several
  /// conjuncts make a fair share of them unsat
  Expr formula() {
    m_pool.clear();
    ExprVector conj;
    for (unsigned i = 0, n = 1 + pick(4); i < n; ++i)
      conj.push_back(boolean(3));
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
      switch (pick(7)) {
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
      switch (pick(10)) {
      case 0:
        e = pick(2) ? mk<BNOT>(bv(w, d)) : mk<BNEG>(bv(w, d));
        break;
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
};

unsigned envOr(const char *name, unsigned dflt) {
  const char *v = std::getenv(name);
  return v ? static_cast<unsigned>(std::strtoul(v, nullptr, 10)) : dflt;
}
} // namespace

TEST_CASE("bitwuzla.random formulas agree with z3") {
  // -- BITWUZLA_FUZZ_N formulas from seed BITWUZLA_FUZZ_SEED; each formula f
  // -- and its negation are solved by the adapter and by Z3. Every sat answer
  // -- is also certified: Z3 checks f under Bitwuzla's values of f's constants.
  Env env;
  EZ3 z3(env.efac);
  RandomFormulas gen(env, envOr("BITWUZLA_FUZZ_SEED", 1));
  const unsigned n = envOr("BITWUZLA_FUZZ_N", 300);

  // -- one adapter for every formula: reset() must clear everything
  bitwuzla_solver_impl adapter;
  Solver &s = adapter;

  unsigned sat = 0, unsat = 0, z3_unknown = 0, disagreements = 0,
           bad_models = 0;
  // -- terms evaluated through the model; values that are not values, or not
  // -- in [0, 2^w); values that differ from Z3's under the same assignment
  unsigned evaluated = 0, non_values = 0, value_mismatches = 0;
  // -- verdicts of the formula check (translation validation) on every f
  std::map<EncodingVerdict, unsigned> encoding;
  Expr f;
  for (unsigned i = 0; i < 2 * n; ++i) {
    f = i % 2 == 0 ? gen.formula() : mk<NEG>(f);

    auto ec = checkBitwuzlaEncoding(f, env.m.encode_term(f), 10000);
    ++encoding[ec.verdict];
    if (ec.verdict != EncodingVerdict::SAME)
      MESSAGE("formula " << i << ": encoding check says "
                         << verdictName(ec.verdict) << ": " << ec.detail);

    s.reset();
    REQUIRE(s.add(f));
    SolverResult r = s.check();
    ZSolver<EZ3> zs(z3);
    zs.assertExpr(f);
    boost::tribool zr = zs.solve();
    if (boost::indeterminate(zr)) {
      ++z3_unknown;
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

    // -- the model, through the Solver interface. Evaluate every term of f,
    // -- and two terms over constants that are in no assertion (Bitwuzla
    // -- completes its model, so they get values too). complete alternates.
    Solver::model_ref model = s.get_model();
    ExprSet seen;
    ExprVector terms;
    termsOf(f, seen, terms);
    std::vector<std::pair<Expr, Expr>> values; // -- term, Bitwuzla's value
    Expr someBv, someBool;
    for (Expr t : terms) {
      Expr v = model->eval(t, values.size() % 2 == 0);
      values.push_back({t, v});
      unsigned w;
      if (!someBv && bv::isBvNum(v, w))
        someBv = mk<BADD>(t, env.bvc("fresh" + std::to_string(w), w));
      if (!someBool && (isOpX<TRUE>(v) || isOpX<FALSE>(v)))
        someBool = mk<XOR>(t, env.boolc("fresh"));
    }
    for (Expr t : {someBv, someBool})
      if (t)
        values.push_back({t, model->eval(t, false)});

    // -- the values of the constants, those in no assertion included, must
    // -- satisfy f for Z3
    ExprSet consts;
    for (auto &tv : values)
      filter(tv.first, bind::IsConst(), std::inserter(consts, consts.begin()));
    ZSolver<EZ3> certify(z3);
    certify.assertExpr(f);
    bool all_values = true;
    for (Expr c : consts) {
      Expr v = model->eval(c, true);
      // -- Z3 cannot take nondet (it would exit); count it below instead
      if (!(isOpX<TRUE>(v) || isOpX<FALSE>(v) || bv::is_bvnum(v))) {
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
                  << z3_unknown << " unknown to z3; encoding check: "
                  << encoding[EncodingVerdict::SAME] << " same; model: "
                  << evaluated << " terms evaluated, " << value_mismatches
                  << " differ from z3, " << non_values << " not values");
  // -- every formula Bitwuzla got is Z3's formula, not only equisatisfiable
  CHECK(encoding[EncodingVerdict::SAME] == 2 * n);
  CHECK(sat + unsat + z3_unknown + disagreements == 2 * n);
  CHECK(disagreements == 0);
  CHECK(bad_models == 0);
  CHECK(z3_unknown == 0);
  CHECK(non_values == 0);
  CHECK(value_mismatches == 0);
  // -- every sat formula has at least one term
  CHECK(evaluated >= sat);
  // -- the generator must produce both kinds, or the test proves little
  CHECK(sat > n / 4);
  CHECK(unsat > n / 4);
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
  bz::Sort arr = env.tm.mk_array_sort(bv8, bv8);
  bz::Term a = env.tm.mk_const(arr, "a");
  CHECK(verdict(x, env.tm.mk_term(bz::Kind::ARRAY_SELECT,
                                  {a, env.m.encode_term(y)}))
            .verdict == EncodingVerdict::UNCHECKED);
  CHECK(
      verdict(x, env.tm.mk_const_array(arr, env.tm.mk_bv_zero(bv8))).verdict ==
      EncodingVerdict::UNCHECKED);

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
  // -- constants of unsupported sorts: integers, arrays (plan 1.6)
  CHECK(env.rejects(mk<EQ>(i, i), i));
  Expr A = bind::mkConst(mkTerm<std::string>("A", env.efac),
                         sort::arrayTy(env.bvsort(8), env.bvsort(8)));
  Expr sel = op::array::select(A, x);
  CHECK(env.rejects(mk<EQ>(sel, x), sel));
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
                         sort::arrayTy(env.bvsort(8), env.bvsort(8)));
  CHECK(isOpX<NONDET>(m->eval(i, true)));
  CHECK(isOpX<NONDET>(m->eval(mk<BV2INT>(x), true)));
  CHECK(isOpX<NONDET>(m->eval(a, true)));
  CHECK(isOpX<NONDET>(m->eval(mk<SELECT>(a, x), false)));
  CHECK(isOpX<NONDET>(m->eval(strct::mk(x, x), false)));

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
  CHECK_FALSE(decode(
      tm.mk_const_array(tm.mk_array_sort(bv8, bv8), tm.mk_bv_zero(bv8))));
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

#endif
