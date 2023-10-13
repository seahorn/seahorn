/**==-- Address Range Map Tests --==*/
#define DOCTEST_CONFIG_IMPLEMENT_WITH_MAIN

#include "doctest.h"
#include "seahorn/Expr/Expr.hh"
#include "seahorn/Expr/ExprAddrRangeMap.hh"
#include "seahorn/Expr/ExprApi.hh"
#include "seahorn/Expr/ExprMemUtils.h"
#include "seahorn/Expr/ExprOpBinder.hh"
#include "seahorn/Expr/ExprOpBool.hh"
#include "seahorn/Expr/ExprOpBv.hh"
#include "llvm/Support/raw_ostream.h"
#include <boost/utility/binary.hpp>

using namespace std;
using namespace expr;
using namespace expr::op;
using namespace expr::addrRangeMap;
using namespace expr::mem;

static bool rangeEq(AddrRange a, AddrRange b) {
  if (!a.isValid() || !b.isValid())
    return false;
  return a.low == b.low && a.high == b.high && a.isBot == b.isBot &&
         a.isTop == b.isTop;
}

static bool armEq(AddrRangeMap &a, AddrRangeMap &b) {
  if (a.size() != b.size())
    return false;

  for (auto aIt = a.cbegin(); aIt != a.cend(); aIt++) {
    auto bIt = b.find(aIt->first);
    if (bIt == b.end())
      return false;

    if (!rangeEq(bIt->second, aIt->second))
      return false;
  }
  return a.isAllTop() == b.isAllTop() && a.isAllBot() == b.isAllBot();
}

static Expr mkBvConst(const std::string name, unsigned width,
                      ExprFactory &efac) {
  return bv::bvConst(mkTerm(name, efac), width);
}

static Expr mkBvNum(mpz_class num, unsigned width, ExprFactory &efac) {
  return bv::bvnum(num, width, efac);
}

static Expr mkAddrBase(unsigned offset, unsigned ptrWidth, ExprFactory &efac) {
  Expr ptrTy = bv::bvsort(ptrWidth, efac);
  Expr base = mkTerm<std::string>("sea.obj", efac);
  return bind::mkConst(op::variant::variant(offset, base), ptrTy);
}

TEST_CASE("expr.addrRangeMap.range.join") {
  AddrRange l(1, 3);
  AddrRange r(2, 4);
  AddrRange top = mkAddrRangeTop();
  AddrRange top2 = mkAddrRangeTop();
  AddrRange bot = mkAddrRangeBot();
  AddrRange bot2 = mkAddrRangeBot();
  /* join [a, b] [c, d] => [min(a, c), max(a, d)]*/
  SUBCASE("join [a, b] [c, d] => [min(a, c), max(b, d)]") {
    AddrRange r0 = l | r;
    CHECK(!r0.isTop);
    CHECK(!r0.isBot);
    CHECK(r0.low == 1);
    CHECK(r0.high == 4);
    CHECK(r0.isValid());
  }
  /* join with top */
  SUBCASE("joining o with top should always yield top") {
    AddrRange r1 = top | r;
    CHECK((bool)r1.isTop);
    CHECK(!r1.isBot);
    CHECK(r1.isValid());

    AddrRange r2 = top | bot;
    CHECK((bool)r2.isTop);
    CHECK(!r2.isBot);
    CHECK(r2.isValid());

    AddrRange r3 = top | top2;
    CHECK((bool)r3.isTop);
    CHECK(!r3.isBot);
    CHECK(r3.isValid());
  }
  /* join with bot */
  SUBCASE("joining o with bot should yield o") {
    AddrRange r4 = l | bot;
    CHECK(rangeEq(r4, l));
    CHECK(r4.isValid());

    AddrRange r5 = bot | bot2;
    CHECK((bool)r5.isBot);
    CHECK(!r5.isTop);
    CHECK(r5.isValid());
  }
}

TEST_CASE("expr.addrRangeMap.range.overlap") {
  AddrRange a(1, 4);
  AddrRange b(2, 6);
  AddrRange top = mkAddrRangeTop();
  AddrRange top2 = mkAddrRangeTop();
  AddrRange bot = mkAddrRangeBot();
  AddrRange bot2 = mkAddrRangeBot();
  /* overlapping ranges with overlap */
  SUBCASE("overlap [a, b] [c, d] => [max(a, c), min(b, d)]") {
    AddrRange ab = a & b;
    CHECK(ab.isValid());
    CHECK(ab.low == 2);
    CHECK(ab.high == 4);
    CHECK(!ab.isBot);
    CHECK(!ab.isTop);
    SUBCASE("overlap [a, b] [c, d] => bot if c < b or a > d") {
      /* overlapping ranges with no overlap */
      AddrRange c(8, 9);
      AddrRange ac = a & c;
      CHECK(ac.isValid());
      CHECK((bool)ac.isBot);
      CHECK(!ac.isTop);
    }
  }

  /* overlapping range with top */
  SUBCASE("overlap o with top should yield o") {
    AddrRange a_top = a & top;
    CHECK(a_top.isValid());
    CHECK(rangeEq(a, a_top));

    AddrRange top_top = top & top2;
    CHECK(top_top.isValid());
    CHECK((bool)top_top.isTop);
    CHECK(!top_top.isBot);

    AddrRange bot_top = top & bot;
    CHECK(bot_top.isValid());
    CHECK((bool)bot_top.isBot);
    CHECK(!bot_top.isTop);
  }

  SUBCASE("overlap o with bot should yield bot") {
    AddrRange a_bot = a & bot;
    CHECK(a_bot.isValid());
    CHECK((bool)a_bot.isBot);
    CHECK(!a_bot.isTop);

    AddrRange bot_bot = bot & bot2;
    CHECK(bot_bot.isValid());
    CHECK(!bot_bot.isTop);
    CHECK((bool)bot_bot.isBot);
  }
}

TEST_CASE("expr.addrRangeMap.range.add") {
  AddrRange a(1, 4);
  AddrRange b(2, 6);
  AddrRange top = mkAddrRangeTop();
  AddrRange top2 = mkAddrRangeTop();
  AddrRange bot = mkAddrRangeBot();
  AddrRange bot2 = mkAddrRangeBot();
  /* overlapping ranges with overlap */
  SUBCASE("add [a, b] [c, d] => [a + c, b + d]") {
    AddrRange ab = a + b;
    CHECK(ab.isValid());
    CHECK(ab.low == a.low + b.low);
    CHECK(ab.high == a.high + b.high);
    CHECK(!ab.isBot);
    CHECK(!ab.isTop);
  }

  /* overlapping range with top */
  SUBCASE("add o with top should yield top") {
    AddrRange a_top = a + top;
    CHECK(a_top.isValid());
    CHECK((bool)a_top.isTop);
    CHECK(!a_top.isBot);

    AddrRange top_top = top + top2;
    CHECK(top_top.isValid());
    CHECK((bool)top_top.isTop);
    CHECK(!top_top.isBot);

    AddrRange bot_top = top + bot;
    CHECK(bot_top.isValid());
    CHECK(!bot_top.isBot);
    CHECK((bool)bot_top.isTop);
  }

  SUBCASE("add o with bot should yield o") {
    AddrRange a_bot = a + bot;
    CHECK(a_bot.isValid());
    CHECK(rangeEq(a_bot, a));

    AddrRange bot_bot = bot + bot2;
    CHECK(bot_bot.isValid());
    CHECK(!bot_bot.isTop);
    CHECK((bool)bot_bot.isBot);
  }
}

TEST_CASE("expr.addrRangeMap.range.build") {
  ExprFactory efac;
  SUBCASE("num(n) => (n, n)") {
    Expr n = mkBvNum(8, 64, efac);
    AddrRange r = addrRangeOf(n);
    CHECK(r.isValid());
    CHECK(r.low == 8);
    CHECK(r.high == 8);
    CHECK(!r.isBot);
    CHECK(!r.isTop);
  }
  SUBCASE("sym(x) => top") {
    Expr x = mkBvConst("x", 32, efac);
    AddrRange r = addrRangeOf(x);
    CHECK(r.isValid());
    CHECK((bool)r.isTop);
    CHECK(!r.isBot);
  }
  SUBCASE("bvadd(a, b): addrRangeOf(a) + addrRangeOf(b)") {
    Expr a = mkBvNum(8, 32, efac);
    Expr b = mkBvNum(16, 32, efac);
    Expr ab = mk<BADD>(a, b);
    AddrRange r = addrRangeOf(ab);
    CHECK(r.isValid());
    CHECK(r.low == 24);
    CHECK(r.high == 24);
    CHECK(!r.isBot);
    CHECK(!r.isTop);
  }
  SUBCASE("ITE(c, x, y): addrRangeOf(x).join(addrRangeOf(y))") {
    Expr a = mkBvNum(8, 32, efac);
    Expr b = mkBvNum(16, 32, efac);
    Expr ite = mk<ITE>(mk<TRUE>(efac), a, b);
    AddrRange r = addrRangeOf(ite);
    CHECK(r.isValid());
    CHECK(r.low == 8);
    CHECK(r.high == 16);
    CHECK(!r.isBot);
    CHECK(!r.isTop);
  }
}

TEST_CASE("expr.addrRangeMap.range.zeroBits") {
  unsigned num = BOOST_BINARY(1111);
  AddrRange a(num, num);
  AddrRange az = zeroBitsRange(a, 2);
  CHECK(az.isValid());
  CHECK(az.low == BOOST_BINARY(1100));
  CHECK(az.high == BOOST_BINARY(1100));

  SUBCASE("zeroBits is no-op on top") {
    AddrRange top = mkAddrRangeTop();
    AddrRange z_top = zeroBitsRange(top, 1);
    CHECK(z_top.isValid());
    CHECK(rangeEq(z_top, top));
  }
  SUBCASE("zeroBits is no-op on bot") {
    AddrRange bot = mkAddrRangeBot();
    AddrRange z_bot = zeroBitsRange(bot, 1);
    CHECK(z_bot.isValid());
    CHECK(rangeEq(z_bot, bot));
  }
}

TEST_CASE("expr.addrRangeMap.union") {
  ExprFactory efac;
  unsigned WIDTH = 32;
  Expr base8 = mkAddrBase(8, WIDTH, efac);
  Expr base16 = mkAddrBase(16, WIDTH, efac);
  Expr base32 = mkAddrBase(32, WIDTH, efac);

  AddrRangeMap a({{base8, AddrRange(0, 8)}, {base16, AddrRange(0, 0)}});
  AddrRangeMap b({{base8, AddrRange(8, 16)},
                  {base16, AddrRange(4, 4)},
                  {base32, mkAddrRangeTop()}});

  AddrRangeMap ab = addrRangeMapUnion(a, b);
  CHECK(ab.isValid());
  CHECK(ab.size() == 3);
  CHECK(!ab.isAllBot());
  CHECK(!ab.isAllTop());
  CHECK(rangeEq(ab[base8], AddrRange(0, 16)));
  CHECK(rangeEq(ab[base16], AddrRange(0, 4)));
  CHECK((bool)ab[base32].isTop);

  AddrRangeMap top = mkARMTop();
  AddrRangeMap top2 = mkARMTop();
  AddrRangeMap bot = mkARMBot();
  AddrRangeMap bot2 = mkARMBot();
  SUBCASE("union with all top should yield all top") {
    AddrRangeMap a_top = addrRangeMapUnion(a, top);
    CHECK(a_top.isValid());
    CHECK(a_top.isAllTop());
    CHECK(!a_top.isAllBot());

    AddrRangeMap bot_top = addrRangeMapUnion(bot, top);
    CHECK(bot_top.isValid());
    CHECK(a_top.isAllTop());
    CHECK(!a_top.isAllBot());

    AddrRangeMap top_top = addrRangeMapUnion(top, top2);
    CHECK(top_top.isValid());
    CHECK(a_top.isAllTop());
    CHECK(!a_top.isAllBot());
  }
  SUBCASE("union o with all bot should yield o") {
    AddrRangeMap b_bot = addrRangeMapUnion(b, bot);
    CHECK(b_bot.isValid());
    CHECK(armEq(b, b_bot));

    AddrRangeMap bot_bot = addrRangeMapUnion(bot, bot2);
    CHECK(bot_bot.isValid());
    CHECK(bot_bot.isAllBot());
    CHECK(!bot_bot.isAllTop());
  }
}

TEST_CASE("expr.addrRangeMap.intersect") {
  ExprFactory efac;
  unsigned WIDTH = 32;
  Expr base8 = mkAddrBase(8, WIDTH, efac);
  Expr base16 = mkAddrBase(16, WIDTH, efac);
  Expr base32 = mkAddrBase(32, WIDTH, efac);

  AddrRangeMap a({{base8, AddrRange(0, 8)}, {base16, AddrRange(0, 0)}});
  AddrRangeMap b({{base8, AddrRange(8, 16)},
                  {base16, AddrRange(4, 4)},
                  {base32, mkAddrRangeTop()}});
  AddrRangeMap c({{base8, AddrRange(0, 0)},
                  {base16, AddrRange(8, 16)},
                  {base32, mkAddrRangeBot()}});

  AddrRangeMap ab = addrRangeMapIntersect(a, b);
  CHECK(ab.isValid());
  CHECK(ab.size() == 1);
  CHECK(!ab.isAllBot());
  CHECK(!ab.isAllTop());
  CHECK(rangeEq(ab[base8], AddrRange(8, 8)));

  SUBCASE("intersect yielding all entries of bot should be all bot") {
    AddrRangeMap bc = addrRangeMapIntersect(b, c);
    CHECK(bc.isValid());
    CHECK(bc.isAllBot());
    CHECK(!bc.isAllTop());
  }

  AddrRangeMap top = mkARMTop();
  AddrRangeMap top2 = mkARMTop();
  AddrRangeMap bot = mkARMBot();
  AddrRangeMap bot2 = mkARMBot();
  SUBCASE("intersect o with all top should yield all o") {
    AddrRangeMap a_top = addrRangeMapIntersect(a, top);
    CHECK(a_top.isValid());
    CHECK(!a_top.isAllTop());
    CHECK(!a_top.isAllBot());
    CHECK(armEq(a_top, a));

    AddrRangeMap bot_top = addrRangeMapIntersect(bot, top);
    CHECK(bot_top.isValid());
    CHECK(!bot_top.isAllTop());
    CHECK(bot_top.isAllBot());

    AddrRangeMap top_top = addrRangeMapIntersect(top, top2);
    CHECK(top_top.isValid());
    CHECK(top_top.isAllTop());
    CHECK(!top_top.isAllBot());
  }
  SUBCASE("intersect o with all bot should yield bot") {
    AddrRangeMap b_bot = addrRangeMapIntersect(b, bot);
    CHECK(b_bot.isValid());
    CHECK(b_bot.isAllBot());
    CHECK(!b_bot.isAllTop());

    AddrRangeMap bot_bot = addrRangeMapIntersect(bot, bot2);
    CHECK(bot_bot.isValid());
    CHECK(bot_bot.isAllBot());
    CHECK(!bot_bot.isAllTop());
  }
}

TEST_CASE("expr.addrRangeMap.build") {
  ExprFactory efac;
  ARMCache c;
  PtrTypeCheckCache ptc;
  Expr base8 = mkAddrBase(8, 32, efac);
  Expr eight = mkBvNum(8, 32, efac);
  Expr eleven = mkBvNum(11, 32, efac);
  Expr base8Plus8 = mk<BADD>(base8, eight);
  Expr base8Plus11 = mk<BADD>(base8, eleven);

  SUBCASE("base addr: {pE => (0, 0)}") {
    AddrRangeMap a = addrRangeMapOf(base8, c, ptc);
    CHECK(a.isValid());
    CHECK(a.size() == 1);
    CHECK(a[base8].low == 0);
    CHECK(a[base8].high == 0);
    CHECK(!a.isAllBot());
    CHECK(!a.isAllTop());
  }
  SUBCASE("zeroBits(x, bits) => addrRangeMapOf(x).zeroBits(bits)") {
    Expr x = bv::concat(bv::extract(31, 2, base8Plus11), bv::bvnum(0, 2, efac));
    AddrRangeMap a = addrRangeMapOf(x, c, ptc);
    CHECK(a.isValid());
    CHECK(a.size() == 1);
    CHECK(a[base8].low == 8); // 11(1111).zeroBits(2) = 8(1000)
    CHECK(a[base8].high == 8);
    CHECK(!a.isAllBot());
    CHECK(!a.isAllTop());
  }
  SUBCASE("bvadd(x, y): addrRangeMapOf(x) + addrRangeMapOf(y)") {
    AddrRangeMap a = addrRangeMapOf(base8Plus8, c, ptc);
    CHECK(a.isValid());
    CHECK(a.size() == 1);
    CHECK(a[base8].low == 8);
    CHECK(a[base8].high == 8);
    CHECK(!a.isAllBot());
    CHECK(!a.isAllTop());
  }
  SUBCASE("ITE(c, x, y): addrRangeMapOf(x) | addrRangeMapOf(y)") {
    Expr ite = mk<ITE>(mk<TRUE>(efac), base8, base8Plus8);
    AddrRangeMap a = addrRangeMapOf(ite, c, ptc);
    CHECK(a.isValid());
    CHECK(a.size() == 1);
    CHECK(a[base8].low == 0);
    CHECK(a[base8].high == 8);
    CHECK(!a.isAllBot());
    CHECK(!a.isAllTop());
  }
}
