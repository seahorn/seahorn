#define DOCTEST_CONFIG_IMPLEMENT_WITH_MAIN
#include "doctest.h"

#include "seahorn/Expr/Expr.hh"
#include "seahorn/Expr/ExprApi.hh"
#include "seahorn/Expr/ExprRewriter.hh"
#include <boost/functional/hash.hpp>

#include "llvm/Support/raw_ostream.h"

#include "seahorn/Support/SeaDebug.h"

using namespace std;
using namespace expr;
using namespace expr::op;
// using namespace seahorn;

static Expr mkAddrBase(unsigned offset, unsigned ptrWidth, ExprFactory &efac) {
  Expr ptrTy = bv::bvsort(ptrWidth, efac);
  Expr base = mkTerm<std::string>("sea.obj", efac);
  return bind::mkConst(op::variant::variant(offset, base), ptrTy);
}

template <class ExpectedIt, class ActualIt>
static void checkPairs(ExpectedIt expectedBegin, ExpectedIt expectedEnd,
                       ActualIt actualBegin, ActualIt actualEnd) {
  CHECK(std::distance(expectedBegin, expectedEnd) ==
        std::distance(actualBegin, actualEnd));
  {
    ExpectedIt e;
    ActualIt a;
    for (e = expectedBegin, a = actualBegin; e != expectedEnd && a != actualEnd;
         e++, a++) {

      CHECK(e->first == a->first);
      CHECK(e->second == a->second);
    }
  }
}

TEST_CASE("expr.store_map.mk") {
  ExprFactory efac;
  op::array::StoreMapCache cache;

  Expr intTy = sort::intTy(efac);
  Expr bvTy = bv::bvsort(32, efac);
  Expr arrTy = sort::arrayTy(intTy, bvTy);
  Expr arr = bind::mkConst(mkTerm<string>("arr", efac), arrTy);

  Expr oA = bv::bvnum(8UL, 32, efac), oB = bv::bvnum(16UL, 32, efac);
  Expr vA = bv::bvConst(mkTerm<string>("A", efac), 32);
  Expr vB = bv::bvConst(mkTerm<string>("B", efac), 32);
  Expr ovB = op::strct::mk(oB, vB), ovA = op::strct::mk(oA, vA);
  Expr base = mkAddrBase(8, 32, efac);
  Expr stMap = op::array::storeMapNew(arr, base, ovA, ovB, cache);
  CHECK(stMap);
  op::array::OffsetValueMap m = {{8UL, vA}, {16UL, vB}};
  checkPairs(m.cbegin(), m.cend(), cache[&*stMap]->cbegin(),
             cache[&*stMap]->cend());
  CHECK(boost::lexical_cast<string>(*stMap) ==
        "store-map(arr, sea.obj_8, cons(struct(8:bv(32), A), "
        "cons(struct(16:bv(32), B))))");
  op::array::clearStoreMapCache(cache);
}

TEST_CASE("expr.store_map.insert") {
  ExprFactory efac;
  op::array::StoreMapCache cache;

  Expr intTy = sort::intTy(efac);
  Expr bvTy = bv::bvsort(32, efac);
  Expr arrTy = sort::arrayTy(intTy, bvTy);
  Expr arr = bind::mkConst(mkTerm<string>("arr", efac), arrTy);

  Expr oA = bv::bvnum(8UL, 32, efac), oB = bv::bvnum(16UL, 32, efac);
  Expr vA = bv::bvConst(mkTerm<string>("A", efac), 32);
  Expr vB = bv::bvConst(mkTerm<string>("B", efac), 32);
  Expr ovB = op::strct::mk(oB, vB), ovA = op::strct::mk(oA, vA);
  Expr base = mkAddrBase(8, 32, efac);
  Expr stMap = op::array::storeMapNew(arr, base, ovA, ovB, cache);
  op::array::OffsetValueMap m = {{8UL, vA}, {16UL, vB}};

  SUBCASE("insert new value") {
    Expr oC = bv::bvnum(24UL, 32, efac);
    Expr vC = bv::bvConst(mkTerm<string>("C", efac), 32);
    stMap = op::array::storeMapInsert(stMap, op::strct::mk(oC, vC), cache);
    m[24UL] = vC;

    CHECK(stMap);
    CHECK(boost::lexical_cast<string>(*stMap) ==
          "store-map(arr, sea.obj_8, cons(struct(24:bv(32), C), "
          "cons(struct(8:bv(32), A), cons(struct(16:bv(32), B)))))");
    op::array::OffsetValueMap *cachedM = cache[&*stMap];
    CHECK(cachedM);
    checkPairs(cachedM->cbegin(), cachedM->cend(), m.cbegin(), m.cend());
    Expr oZ = bv::bvnum(0UL, 32, efac);
    Expr vZ = bv::bvConst(mkTerm<string>("Z", efac), 32);
    stMap = op::array::storeMapInsert(stMap, op::strct::mk(oZ, vZ), cache);
    m[0UL] = vZ;

    CHECK(stMap);
    CHECK(boost::lexical_cast<string>(*stMap) ==
          "store-map(arr, sea.obj_8, cons(struct(0:bv(32), Z), "
          "cons(struct(24:bv(32), C), cons(struct(8:bv(32), A), "
          "cons(struct(16:bv(32), B))))))");
    cachedM = cache[&*stMap];
    CHECK(cachedM);
    checkPairs(cachedM->cbegin(), cachedM->cend(), m.cbegin(), m.cend());
  }
  SUBCASE("update value") {
    Expr newVB = bv::bvConst(mkTerm<string>("new-B", efac), 32);
    stMap = op::array::storeMapInsert(stMap, op::strct::mk(oB, newVB), cache);
    m[op::bv::toMpz(oB).get_ui()] = newVB;
    op::array::OffsetValueMap *cached = cache[&*stMap];

    CHECK(stMap);
    CHECK(cached);
    checkPairs(m.cbegin(), m.cend(), cached->cbegin(), cached->cend());
    CHECK(boost::lexical_cast<string>(*stMap) ==
          "store-map(arr, sea.obj_8, cons(struct(16:bv(32), new-B), "
          "cons(struct(8:bv(32), A), cons(struct(16:bv(32), B)))))");

    // CHECK(boost::lexical_cast<string>(*stMap) == "store-map(arr, sea.obj_8,
    // tuple(struct(8:bv(32), A), struct(16:bv(32), new-B)))");
    Expr newVA = bv::bvConst(mkTerm<string>("new-A", efac), 32);
    stMap = op::array::storeMapInsert(stMap, op::strct::mk(oA, newVA), cache);
    m[op::bv::toMpz(oA).get_ui()] = newVA;
    cached = cache[&*stMap];

    CHECK(stMap);
    CHECK(cached);
    checkPairs(m.cbegin(), m.cend(), cached->cbegin(), cached->cend());
    CHECK(boost::lexical_cast<string>(*stMap) ==
          "store-map(arr, sea.obj_8, cons(struct(8:bv(32), new-A), "
          "cons(struct(16:bv(32), new-B), cons(struct(8:bv(32), A), "
          "cons(struct(16:bv(32), B))))))");
  }
  op::array::clearStoreMapCache(cache);
}

TEST_CASE("expr.store_map.find") {
  ExprFactory efac;
  op::array::StoreMapCache cache;

  Expr intTy = sort::intTy(efac);
  Expr bvTy = bv::bvsort(32, efac);
  Expr arrTy = sort::arrayTy(intTy, bvTy);
  Expr arr = bind::mkConst(mkTerm<string>("arr", efac), arrTy);

  Expr oA = bv::bvnum(8UL, 32, efac);
  Expr oB = bv::bvnum(16UL, 32, efac);
  Expr oC = bv::bvnum(24UL, 32, efac);
  Expr vA = bv::bvConst(mkTerm<string>("A", efac), 32);
  Expr vB = bv::bvConst(mkTerm<string>("B", efac), 32);
  Expr vC = bv::bvConst(mkTerm<string>("C", efac), 32);

  Expr ovB = op::strct::mk(oB, vB), ovA = op::strct::mk(oA, vA),
       ovC = op::strct::mk(oC, vC);
  Expr base = mkAddrBase(8, 32, efac);
  Expr stMap = op::array::storeMapNew(arr, base, ovA, ovB, cache);
  stMap = op::array::storeMapInsert(stMap, ovC, cache);

  SUBCASE("found") {
    Expr findA =
        op::array::storeMapFind(stMap, bv::bvnum(8UL, 32, efac), cache);
    CHECK(findA);
    CHECK(findA == vA);

    Expr findB =
        op::array::storeMapFind(stMap, bv::bvnum(16UL, 32, efac), cache);
    CHECK(findB);
    CHECK(findB == vB);

    Expr findC =
        op::array::storeMapFind(stMap, bv::bvnum(24UL, 32, efac), cache);
    CHECK(findC);
    CHECK(findC == vC);
  }

  SUBCASE("not found") {
    Expr notFound =
        op::array::storeMapFind(stMap, bv::bvnum(100UL, 32, efac), cache);
    CHECK(!notFound);
  }
  op::array::clearStoreMapCache(cache);
}

TEST_CASE("expr.store_map.rewrite-wow") {
  // using namespace expr::addrRangeMap;
  ExprFactory efac;

  Expr intTy = sort::intTy(efac);
  Expr bvTy = bv::bvsort(32, efac);
  Expr arrTy = sort::arrayTy(intTy, bvTy);
  Expr initialArr = bind::mkConst(mkTerm<string>("arr", efac), arrTy);

  Expr base = mkAddrBase(8, 32, efac);

  DagVisitCache cache;
  op::array::StoreMapCache smapCache;
  WriteOverWriteConfig wowC(efac, cache, smapCache, 32);

  /* Some common Memory Expressions */
  Expr oA = bv::bvnum(8UL, 32, efac);
  Expr oB = bv::bvnum(16UL, 32, efac);
  Expr oC = bv::bvnum(24UL, 32, efac);
  Expr vA = bv::bvConst(mkTerm<string>("A", efac), 32);
  Expr vB = bv::bvConst(mkTerm<string>("B", efac), 32);
  Expr vC = bv::bvConst(mkTerm<string>("C", efac), 32);
  Expr storeInner = op::array::store(initialArr, base, vA);
  Expr ovB = op::strct::mk(oB, vB), ovA = op::strct::mk(oA, vA),
       ovC = op::strct::mk(oC, vC);

  SUBCASE("STORE-COMMUTE") {
    Expr iBase = mkAddrBase(4, 32, efac);
    Expr storeE = op::array::store(storeInner, iBase, vB);
    ExprRewriter<WriteOverWriteConfig> rw(storeE->efac(), wowC, cache);
    Expr res = rw.rewriteExpr(storeE);
    CHECK(res);
    CHECK(boost::lexical_cast<string>(*res) ==
          "store(store(arr, sea.obj_4, B), sea.obj_8, A)");

    // push down multiple levels
    Expr idx = mk<BADD>(iBase, oA);
    storeE = op::array::store(res, idx, vC);
    res = rw.rewriteExpr(storeE);
    CHECK(res);
    CHECK(boost::lexical_cast<string>(*res) ==
          "store(store-map(arr, sea.obj_4, cons(struct(8:bv(32), C), "
          "cons(struct(0:bv(32), B)))), sea.obj_8, A)");
    /* check store map is fine */
    op::array::OffsetValueMap expected = {{8UL, vC}, {0UL, vB}};
    Expr smap = res->arg(0);
    op::array::OffsetValueMap *cached = smapCache[&*smap];
    CHECK(cached);
    checkPairs(expected.cbegin(), expected.cend(), cached->cbegin(),
               cached->cend());

    Expr extremeBase = mkAddrBase(0, 32, efac);

    storeE = op::array::store(res, extremeBase, vC);
    res = rw.rewriteExpr(storeE);
    CHECK(res);
    CHECK(
        boost::lexical_cast<string>(*res) ==
        "store(store-map(store(arr, sea.obj_0, C), sea.obj_4, "
        "cons(struct(8:bv(32), C), cons(struct(0:bv(32), B)))), sea.obj_8, A)");
    smap = res->arg(0);
    cached = smapCache[&*smap];
    CHECK(cached);
    // no change to cache
    checkPairs(expected.cbegin(), expected.cend(), cached->cbegin(),
               cached->cend());
  }

  SUBCASE("SMAP-NEW") {
    op::array::OffsetValueMap expected = {{8UL, vB}, {0UL, vA}};
    Expr storeE = op::array::store(
        storeInner, mk<BADD>(base, bv::bvnum(8UL, 32, efac)), vB);
    ExprRewriter<WriteOverWriteConfig> rw(storeE->efac(), wowC, cache);
    Expr res = rw.rewriteExpr(storeE);
    CHECK(res);
    CHECK(boost::lexical_cast<string>(*res) ==
          "store-map(arr, sea.obj_8, cons(struct(8:bv(32), B), "
          "cons(struct(0:bv(32), A))))");
    op::array::OffsetValueMap *cached = smapCache[&*res];
    checkPairs(expected.begin(), expected.end(), cached->begin(),
               cached->end());
    SUBCASE("SMAP-NEW should not trigger if two offsets are equal") {
      Expr storeEEdge = op::array::store(storeInner, base, vB);
      ExprRewriter<WriteOverWriteConfig> rw(storeEEdge->efac(), wowC, cache);
      Expr res = rw.rewriteExpr(storeEEdge);
      CHECK(res);
      CHECK(boost::lexical_cast<string>(*res) == "store(arr, sea.obj_8, B)");
    }
  }

  SUBCASE("SMAP-HIT") {
    Expr stMap = op::array::storeMapNew(initialArr, base, ovA, ovB, smapCache);
    stMap = op::array::storeMapInsert(stMap, ovC, smapCache);
    using namespace op::bv;
    op::array::OffsetValueMap expected = {{toMpz(oA).get_ui(), vA},
                                          {toMpz(oB).get_ui(), vB},
                                          {toMpz(oC).get_ui(), vC}};

    Expr oD = bv::bvnum(12UL, 32, efac);
    Expr vD = bv::bvConst(mkTerm<string>("D", efac), 32);
    Expr storeE = op::array::store(stMap, mk<BADD>(base, oD), vD);
    ExprRewriter<WriteOverWriteConfig> rw(storeE->efac(), wowC, cache);
    Expr res = rw.rewriteExpr(storeE);
    expected[toMpz(oD).get_ui()] = vD;
    CHECK(res);
    op::array::OffsetValueMap *cached = smapCache[&*res];
    checkPairs(cached->cbegin(), cached->cend(), expected.cbegin(),
               expected.cend());
    CHECK(boost::lexical_cast<string>(*res) ==
          "store-map(arr, sea.obj_8, cons(struct(12:bv(32), D), "
          "cons(struct(24:bv(32), C), cons(struct(8:bv(32), A), "
          "cons(struct(16:bv(32), B))))))");

    /* update */
    Expr vDNew = bv::bvConst(mkTerm<string>("DD", efac), 32);
    Expr storeEE = op::array::store(res, mk<BADD>(base, oD), vDNew);
    res = rw.rewriteExpr(storeEE);
    CHECK(res);
    cached = smapCache[&*res];
    expected[toMpz(oD).get_ui()] = vDNew;
    checkPairs(cached->cbegin(), cached->cend(), expected.cbegin(),
               expected.cend());
    CHECK(boost::lexical_cast<string>(*res) ==
          "store-map(arr, sea.obj_8, cons(struct(12:bv(32), DD), "
          "cons(struct(12:bv(32), D), cons(struct(24:bv(32), C), "
          "cons(struct(8:bv(32), A), cons(struct(16:bv(32), B)))))))");
  }

  SUBCASE("SMAP-COMMUTE") {
    Expr stMap = op::array::storeMapNew(initialArr, base, ovA, ovB, smapCache);
    stMap = op::array::storeMapInsert(stMap, ovC, smapCache);
    using namespace op::bv;
    op::array::OffsetValueMap expected = {{toMpz(oA).get_ui(), vA},
                                          {toMpz(oB).get_ui(), vB},
                                          {toMpz(oC).get_ui(), vC}};

    Expr oBase = mkAddrBase(4, 32, efac);
    Expr vO = bv::bvConst(mkTerm<string>("O", efac), 32);
    ExprRewriter<WriteOverWriteConfig> rw(efac, wowC, cache);
    SUBCASE("concrete offset") {
      Expr storeE = op::array::store(stMap, oBase, vO);
      Expr res = rw.rewriteExpr(storeE);
      CHECK(res);
      op::array::OffsetValueMap *actual = smapCache[&*res];
      checkPairs(expected.cbegin(), expected.cend(), actual->cbegin(),
                 actual->cend());
      CHECK(boost::lexical_cast<string>(*res) ==
            "store-map(store(arr, sea.obj_4, O), sea.obj_8, "
            "cons(struct(24:bv(32), C), cons(struct(8:bv(32), A), "
            "cons(struct(16:bv(32), B)))))");
    }
    SUBCASE("symbolic offset") {
      /* should work with symbolic or ite as long as base is unique and
       * different from inner */
      Expr storeE = op::array::store(stMap, mk<BADD>(oBase, vO), vO);
      Expr res = rw.rewriteExpr(storeE);
      CHECK(res);
      op::array::OffsetValueMap *actual = smapCache[&*res];
      checkPairs(expected.cbegin(), expected.cend(), actual->cbegin(),
                 actual->cend());
      CHECK(boost::lexical_cast<string>(*res) ==
            "store-map(store(arr, bvadd(sea.obj_4, O), O), sea.obj_8, "
            "cons(struct(24:bv(32), C), cons(struct(8:bv(32), A), "
            "cons(struct(16:bv(32), B)))))");
    }
    SUBCASE("already in descending order") {
      oBase = mkAddrBase(16, 32, efac);
      vO = bv::bvConst(mkTerm<string>("O", efac), 32);
      Expr storeE = op::array::store(stMap, oBase, vO);
      Expr res = rw.rewriteExpr(storeE);
      op::array::OffsetValueMap *actual = smapCache[&*(res->arg(0))];
      checkPairs(expected.cbegin(), expected.cend(), actual->cbegin(),
                 actual->cend());
      CHECK(res);
      CHECK(boost::lexical_cast<string>(*res) ==
            "store(store-map(arr, sea.obj_8, cons(struct(24:bv(32), C), "
            "cons(struct(8:bv(32), A), cons(struct(16:bv(32), B))))), "
            "sea.obj_16, O)");
    }
  }

  SUBCASE("SMAP no rewrite") {
    Expr stMap = op::array::storeMapNew(initialArr, base, ovA, ovB, smapCache);
    stMap = op::array::storeMapInsert(stMap, ovC, smapCache);
    Expr oBase = mkAddrBase(128, 32, efac);
    Expr vO = bv::bvConst(mkTerm<string>("O", efac), 32);
    ExprRewriter<WriteOverWriteConfig> rw(efac, wowC, cache);

    SUBCASE("store same base but symbolic offset into store-map") {
      Expr storeE = op::array::store(stMap, mk<BADD>(base, vO), vO);
      Expr res = rw.rewriteExpr(storeE);
      CHECK(res);
      CHECK(res == storeE);
    }
    SUBCASE("store into symbolic or ITE address") {
      Expr symAddr = mk<ITE>(mk<EQ>(vA, vB), base, oBase);
      Expr storeE = op::array::store(stMap, symAddr, vO);
      Expr res = rw.rewriteExpr(storeE);
      CHECK(res);
      CHECK(res == storeE);
    }
  }

  SUBCASE("Test erasure of long chain of stores") {
    // store multiple times into obj_8, obj_16 and obj_16 + 8
    // the end result should just be stmap(obj_16...) -> store(obj_8...)
    using namespace op::array;
    Expr xBase = mkAddrBase(16, 32, efac);
    Expr mem =
        store(store(store(store(store(store(initialArr, xBase, vA), base, vB),
                                mk<BADD>(xBase, oA), vC),
                          base, vA),
                    xBase, vB),
              mk<BADD>(xBase, oA), vA);
    OffsetValueMap expected = {{0UL, vB}, {8UL, vA}};
    ExprRewriter<WriteOverWriteConfig> rw(efac, wowC, cache);
    Expr res = rw.rewriteExpr(mem);
    CHECK(res);
    OffsetValueMap *actual = smapCache[&*res];
    CHECK(actual);
    checkPairs(expected.cbegin(), expected.cend(), actual->cbegin(),
               actual->cend());
    std::cout << *res << std::endl;
    CHECK(boost::lexical_cast<string>(*res) ==
          "store-map(store(arr, sea.obj_8, A), sea.obj_16, "
          "cons(struct(8:bv(32), A), cons(struct(0:bv(32), B), "
          "cons(struct(8:bv(32), C), cons(struct(0:bv(32), A))))))");
  }
  clearENodePtrCache(cache);
  op::array::clearStoreMapCache(smapCache);
}

TEST_CASE("Read over mem with store-map") {
  ExprFactory efac;

  Expr intTy = sort::intTy(efac);
  Expr bvTy = bv::bvsort(32, efac);
  Expr arrTy = sort::arrayTy(intTy, bvTy);
  Expr initialArr = bind::mkConst(mkTerm<string>("arr", efac), arrTy);

  Expr base = mkAddrBase(8, 32, efac);

  DagVisitCache cache;
  ARMCache aCache;
  PtrTypeCheckCache ptcCache;
  op::array::StoreMapCache smapCache;

  ITECompRewriteConfig conf(efac, cache, aCache, ptcCache, smapCache, 8, 32);
  ExprRewriter<ITECompRewriteConfig> rw(efac, conf, cache);

  /* Some common Memory Expressions */
  Expr oA = bv::bvnum(8UL, 32, efac);
  Expr oB = bv::bvnum(16UL, 32, efac);
  Expr oC = bv::bvnum(24UL, 32, efac);
  Expr vA = bv::bvConst(mkTerm<string>("A", efac), 32);
  Expr vB = bv::bvConst(mkTerm<string>("B", efac), 32);
  Expr vC = bv::bvConst(mkTerm<string>("C", efac), 32);
  Expr storeInner = op::array::store(initialArr, base, vA);
  Expr ovB = op::strct::mk(oB, vB), ovA = op::strct::mk(oA, vA),
       ovC = op::strct::mk(oC, vC);
  Expr stMap = op::array::storeMapNew(initialArr, base, ovB, ovA, smapCache);
  stMap = op::array::storeMapInsert(stMap, ovC, smapCache);
  SUBCASE("R-HIT") {
    Expr idx = mk<BADD>(base, oA);
    Expr row = op::array::select(stMap, idx);
    Expr res = rw.rewriteExpr(row);
    CHECK(res);
    CHECK(boost::lexical_cast<string>(*res) == "A");
  }
  SUBCASE("R-MISS") {
    Expr oD = bv::bvnum(32UL, 32, efac);
    Expr idx = mk<BADD>(base, oD);
    Expr row = op::array::select(stMap, idx);
    Expr res = rw.rewriteExpr(row);
    CHECK(res);
    CHECK(boost::lexical_cast<string>(*res) ==
          "select(arr, bvadd(sea.obj_8, 32:bv(32)))");
  }
  SUBCASE("R-SKIP") {
    Expr otherBase = mkAddrBase(108, 32, efac);
    Expr idx = mk<BADD>(otherBase, oA);
    Expr row = op::array::select(stMap, idx);
    Expr res = rw.rewriteExpr(row);
    CHECK(res);
    CHECK(boost::lexical_cast<string>(*res) ==
          "select(arr, bvadd(sea.obj_108, 8:bv(32)))");
  }

  SUBCASE("R-ABORT") {
    SUBCASE("same base, symbolic offset") {
      Expr idx = mk<BADD>(base, vA);
      Expr row = op::array::select(stMap, idx);
      Expr res = rw.rewriteExpr(row);
      CHECK(res);
      CHECK(boost::lexical_cast<string>(*res) ==
            "ite(A=(24:bv(32)), C, ite(A=(16:bv(32)), B, ite(A=(8:bv(32)), A, "
            "select(arr, bvadd(sea.obj_8, A)))))");
    }

    SUBCASE("unknown base") {
      Expr idx = vA;
      Expr row = op::array::select(stMap, idx);
      Expr res = rw.rewriteExpr(row);
      CHECK(res);
      CHECK(boost::lexical_cast<string>(*res) ==
            "ite(A=bvadd(sea.obj_8, 24:bv(32)), C, ite(A=bvadd(sea.obj_8, "
            "16:bv(32)), B, ite(A=bvadd(sea.obj_8, 8:bv(32)), A, select(arr, "
            "A))))");
    }

    SUBCASE("lowest level R-O-W should be rewritten") {
      Expr inner = op::array::store(initialArr, mkAddrBase(16, 32, efac), vC);
      stMap = op::array::storeMapNew(inner, base, ovA, ovB, smapCache);
      Expr idx = vA;
      Expr row = op::array::select(stMap, idx);
      Expr res = rw.rewriteExpr(row);
      CHECK(res);
      CHECK(boost::lexical_cast<string>(*res) ==
            "ite(A=bvadd(sea.obj_8, 16:bv(32)), B, ite(A=bvadd(sea.obj_8, "
            "8:bv(32)), A, ite(A=sea.obj_16, C, select(arr, A))))");
    }
  }
  clearENodePtrCache(cache);
  clearENodePtrCache(ptcCache);
  clearENodePtrCache(aCache);
  op::array::clearStoreMapCache(smapCache);
}
