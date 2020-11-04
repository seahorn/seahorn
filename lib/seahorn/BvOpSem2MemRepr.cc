#include "BvOpSem2Context.hh"
#include "seahorn/Expr/ExprOpBinder.hh"
namespace {
template <typename T, typename... Rest>
auto as_std_array(const T &t, const Rest &... rest) ->
    typename std::array<T, sizeof...(Rest) + 1> {
  return {t, rest...};
}
} // namespace

#define DEBUG_TYPE "opsem"

namespace seahorn {
namespace details {

// MemSet operates at word level.
// _val must fit within a byte
// _val is converted to a byte.
// byte is converted to a word
// e.g. _val = 0x1, len = 0x1, wordSzInBytes = 0x4 => 0x00000001
// e.g. _val = 0x1, len = 0x4, wordSzInBytes = 0x4 => 0x00000001
Expr OpSemMemArrayRepr::MemSet(Expr ptr, Expr _val, unsigned len, Expr mem,
                               unsigned wordSzInBytes, Expr ptrSort,
                               uint32_t align) {
  Expr res;

  unsigned width;
  if (bv::isBvNum(_val, width) && width == 8) {
    assert(wordSzInBytes <= sizeof(unsigned long));
    int byte = bv::toMpz(_val).get_ui();
    unsigned long val = 0;
    memset(&val, byte, wordSzInBytes);

    res = mem;
    for (unsigned i = 0; i < len; i += wordSzInBytes) {
      Expr idx = m_memManager.ptrAdd(ptr, i);
      res = op::array::store(
          res, idx, bv::bvnum(val, wordSzInBytes * m_BitsPerByte, m_efac));
    }
    return res;
  }

  return res;
}

// len is in bytes
// _val must fit within a byte
Expr OpSemMemArrayRepr::MemSet(Expr ptr, Expr _val, Expr len, Expr mem,
                               unsigned wordSzInBytes, Expr ptrSort,
                               uint32_t align) {
  Expr res;

  unsigned width;
  Expr bvVal;
  // extend _val to current word size
  if (bv::isBvNum(_val, width)) {
    assert(width == 8);
    assert(wordSzInBytes <= sizeof(unsigned long));
    int byte = bv::toMpz(_val).get_ui();
    unsigned long val = 0;
    memset(&val, byte, wordSzInBytes);
    bvVal = bv::bvnum(val, wordSzInBytes * m_BitsPerByte, m_efac);
  } else {
    bvVal = _val;
    for (unsigned i = 1; i < wordSzInBytes; ++i) {
      bvVal = m_ctx.alu().Concat({bvVal, 8}, {bvVal, 8 * i});
    }
  }

  // write into memory
  res = mem;
  // XXX assume that bit-width(len) == ptrSzInBits
  auto bitWidth = m_memManager.ptrSzInBits();
  Expr upperBound = m_ctx.alu().doAdd(
      len, m_ctx.alu().si(-wordSzInBytes, bitWidth), bitWidth);

  for (unsigned i = 0; i < m_memCpyUnrollCnt; i += wordSzInBytes) {
    Expr idx = m_memManager.ptrAdd(ptr, i);
    auto cmp = m_ctx.alu().doUle(m_ctx.alu().si(i, m_memManager.ptrSzInBits()),
                                 upperBound, m_memManager.ptrSzInBits());
    Expr ite = boolop::lite(cmp, bvVal, op::array::select(mem, idx));
    res = op::array::store(res, idx, ite);
  }

  LOG("opsem.array", errs() << "memset: " << *res << "\n";);
  return res;
}

// TODO: This function is untested
Expr OpSemMemArrayRepr::MemCpy(Expr dPtr, Expr sPtr, Expr len,
                               Expr memTrsfrRead, Expr memRead,
                               unsigned wordSzInBytes, Expr ptrSort,
                               uint32_t align) {
  (void)ptrSort;

  Expr res = memRead;
  Expr srcMem = memTrsfrRead;
  if (wordSzInBytes == 1 || (wordSzInBytes == 4 && align == 4) ||
      (wordSzInBytes == 8 && (align == 4 || align == 8)) ||
      m_memManager.isIgnoreAlignment()) {
    // XXX assume that bit-width(len) == ptrSzInBits
    auto bitWidth = m_memManager.ptrSzInBits();
    Expr upperBound = m_ctx.alu().doAdd(
        len, m_ctx.alu().si(-wordSzInBytes, bitWidth), bitWidth);
    for (unsigned i = 0; i < m_memCpyUnrollCnt; i += wordSzInBytes) {
      Expr dIdx = m_memManager.ptrAdd(dPtr, i);
      Expr sIdx = m_memManager.ptrAdd(sPtr, i);
      auto cmp =
          m_ctx.alu().doUle(m_ctx.alu().si(i, m_memManager.ptrSzInBits()),
                            upperBound, m_memManager.ptrSzInBits());
      auto ite = boolop::lite(cmp, op::array::select(srcMem, sIdx),
                              op::array::select(memRead, dIdx));
      res = op::array::store(res, dIdx, ite);
    }
    LOG("opsem.array", INFO << "memcpy: " << *res << "\n";);

  } else {
    DOG(ERR << "Word size and pointer are not aligned and "
               "alignment is not ignored!");
    assert(false);
  }
  return res;
}

Expr OpSemMemArrayRepr::MemCpy(Expr dPtr, Expr sPtr, unsigned len,
                               Expr memTrsfrRead, Expr memRead,
                               unsigned wordSzInBytes, Expr ptrSort,
                               uint32_t align) {
  (void)ptrSort;

  Expr res;

  if (wordSzInBytes == 1 || (wordSzInBytes == 4 && align == 4) ||
      (wordSzInBytes == 8 && (align == 4 || align == 8)) ||
      m_memManager.isIgnoreAlignment()) {
    Expr srcMem = memTrsfrRead;
    res = memRead;
    for (unsigned i = 0; i < len; i += wordSzInBytes) {
      Expr dIdx = m_memManager.ptrAdd(dPtr, i);
      Expr sIdx = m_memManager.ptrAdd(sPtr, i);

      Expr val = op::array::select(srcMem, sIdx);
      res = op::array::store(res, dIdx, val);
    }
  } else {
    LOG("opsem.array", ERR << "Word size and pointer are not aligned and "
                              "alignment is not ignored!"
                           << "\n");
    assert(false);
  }
  return res;
}

Expr OpSemMemArrayRepr::MemFill(Expr dPtr, char *sPtr, unsigned len, Expr mem,
                                unsigned wordSzInBytes, Expr ptrSort,
                                uint32_t align) {
  Expr res = mem;
  const unsigned sem_word_sz = wordSzInBytes;

  // 8 bytes because assumed largest supported sem_word_sz = 8
  assert(sizeof(unsigned long) >= sem_word_sz);

  for (unsigned i = 0; i < len; i += sem_word_sz) {
    Expr dIdx = m_memManager.ptrAdd(dPtr, i);
    // copy bytes from buffer to word - word must accommodate largest
    // supported word size
    // 8 bytes because assumed largest supported sem_word_sz = 8
    unsigned long word = 0;
    std::memcpy(&word, sPtr + i, sem_word_sz);
    Expr val = bv::bvnum(word, wordSzInBytes * m_BitsPerByte, m_efac);
    res = op::array::store(res, dIdx, val);
  }
  return res;
}

Expr OpSemMemLambdaRepr::storeAlignedWordToMem(Expr val, Expr ptr, Expr ptrSort,
                                               Expr mem) {
  Expr b0 = bind::bvar(0, ptrSort);

  Expr fappl = op::bind::fapp(mem, b0);
  Expr ite = boolop::lite(m_memManager.ptrEq(b0, ptr), val, fappl);

  Expr addr = bind::mkConst(mkTerm<std::string>("addr", m_efac), ptrSort);
  Expr decl = bind::fname(addr);
  return mk<LAMBDA>(decl, ite);
}

// len is in bytes
Expr OpSemMemLambdaRepr::MemSet(Expr ptr, Expr _val, unsigned len, Expr mem,
                                unsigned wordSzInBytes, Expr ptrSort,
                                uint32_t align) {
  Expr res;
  Expr bvVal;
  unsigned width;
  // -- expected width of 8 bits
  if (m_ctx.alu().isNum(_val, width)) {
    assert(width == 8);
    assert(wordSzInBytes <= sizeof(unsigned long));
    int byte = bv::toMpz(_val).get_ui();
    unsigned long val = 0;
    memset(&val, byte, wordSzInBytes);
    bvVal = bv::bvnum(val, wordSzInBytes * m_BitsPerByte, m_efac);
  } else {
    bvVal = _val;
    for (unsigned i = 1; i < wordSzInBytes; ++i) {
      bvVal = m_ctx.alu().Concat({bvVal, 8}, {bvVal, 8 * i});
    }
  }

  assert(bvVal);

  res = mem;

  Expr last = m_memManager.ptrAdd(ptr, len - wordSzInBytes);
  Expr b0 = bind::bvar(0, ptrSort);

  Expr cmp = m_memManager.ptrInRangeCheck(ptr, b0, last);
  Expr fappl = op::bind::fapp(res, b0);
  Expr ite = boolop::lite(cmp, bvVal, fappl);

  Expr addr = bind::mkConst(mkTerm<std::string>("addr", m_efac), ptrSort);
  Expr decl = bind::fname(addr);
  res = mk<LAMBDA>(decl, ite);
  LOG("opsem.lambda", errs() << "MemSet " << *res << "\n");

  return res;
}

Expr OpSemMemLambdaRepr::MemSet(Expr ptr, Expr _val, Expr len, Expr mem,
                                unsigned wordSzInBytes, Expr ptrSort,
                                uint32_t align) {
  Expr res;
  Expr val;

  DOG(if (wordSzInBytes != 1) WARN << "memset: untested word size: "
                                   << wordSzInBytes);

  unsigned width;
  if (bv::isBvNum(_val, width)) {
    assert(width == 8);
    assert(wordSzInBytes <= sizeof(unsigned long));
    int byte = bv::toMpz(_val).get_ui();
    unsigned long uval = 0;
    if (byte)
      memset(&uval, byte, wordSzInBytes);
    val = m_ctx.alu().si(uval, wordSzInBytes * 8);
  } else {
    val = _val;
    for (unsigned i = 1; i < wordSzInBytes; ++i) {
      val = m_ctx.alu().Concat({val, 8}, {val, 8 * i});
    }
  }
  assert(val);

  Expr last =
      m_memManager.ptrAdd(m_memManager.ptrAdd(ptr, len), -wordSzInBytes);

  Expr bvVal = val;
  Expr b0 = bind::bvar(0, ptrSort);

  Expr cmp = m_memManager.ptrInRangeCheck(ptr, b0, last);
  Expr fappl = op::bind::fapp(mem, b0);
  Expr ite = boolop::lite(cmp, bvVal, fappl);

  Expr addr = bind::mkConst(mkTerm<std::string>("addr", m_efac), ptrSort);
  Expr decl = bind::fname(addr);
  res = mk<LAMBDA>(decl, ite);
  LOG("opsem.lambda", errs() << "MemSet " << *res << "\n");

  return res;
}

Expr OpSemMemLambdaRepr::MemCpy(Expr dPtr, Expr sPtr, Expr len,
                                Expr memTrsfrRead, Expr memRead,
                                unsigned wordSzInBytes, Expr ptrSort,
                                uint32_t align) {
  Expr res;
  Expr srcMem = memTrsfrRead;
  // address of the last word that is copied into dst
  Expr dstLast =
      m_memManager.ptrAdd(m_memManager.ptrAdd(dPtr, len), -wordSzInBytes);
  res = createMemCpyExpr(dPtr, sPtr, memRead, ptrSort, srcMem, dstLast,
                         wordSzInBytes, align);
  return res;
}

// TODO: Call this from concrete LambdaRepr::MemCpy also to
// remove duplicate code
Expr OpSemMemLambdaRepr::createMemCpyExpr(
    const Expr &dPtr, const Expr &sPtr, const Expr &memRead,
    const Expr &ptrSort, const Expr &srcMem, const Expr &dstLast,
    unsigned wordSzInBytes, uint32_t align) const {
  Expr res;
  if (wordSzInBytes == 1 || (wordSzInBytes == 4 && align == 4) ||
      (wordSzInBytes == 8 && (align == 4 || align == 8)) ||
      m_memManager.isIgnoreAlignment()) {
    Expr b0 = bind::bvar(0, ptrSort);
    // -- dPtr <= b0 <= dstLast
    Expr cmp = this->m_memManager.ptrInRangeCheck(dPtr, b0, dstLast);
    // -- offset == dPtr - sPtr
    Expr offset = this->m_memManager.ptrOffsetFromBase(dPtr, sPtr);
    // -- maps ptr in dst to ptr in src
    Expr readPtrInSrc = this->m_memManager.ptrAdd(b0, offset);

    Expr readFromSrc = bind::fapp(srcMem, readPtrInSrc);
    Expr readFromDst = bind::fapp(memRead, b0);

    Expr ite = boolop::lite(cmp, readFromSrc, readFromDst);
    Expr addr =
        bind::mkConst(mkTerm<std::string>("addr", this->m_efac), ptrSort);
    Expr decl = bind::fname(addr);
    res = mk<LAMBDA>(decl, ite);
    LOG("opsem.lambda", errs() << "MemCpy " << *res << "\n");
  } else {
    DOG(ERR << "unsupported memcpy due to size and/or alignment.";);
    DOG(WARN << "Interpreting memcpy as noop");
    res = memRead;
  }
  return res;
}

Expr OpSemMemLambdaRepr::MemCpy(Expr dPtr, Expr sPtr, unsigned len,
                                Expr memTrsfrRead, Expr memRead,
                                unsigned wordSzInBytes, Expr ptrSort,
                                uint32_t align) {
  Expr res;

  if (wordSzInBytes == 1 || (wordSzInBytes == 4 && align == 4) ||
      (wordSzInBytes == 8 && (align == 4 || align == 8)) ||
      m_memManager.isIgnoreAlignment()) {
    Expr srcMem = memTrsfrRead;

    if (len > 0) {
      unsigned bytesToCpy = len - wordSzInBytes;
      Expr dstLast = m_memManager.ptrAdd(dPtr, bytesToCpy);

      Expr b0 = bind::bvar(0, ptrSort);
      Expr cmp = m_memManager.ptrInRangeCheck(dPtr, b0, dstLast);
      Expr offset = m_memManager.ptrOffsetFromBase(dPtr, sPtr);
      Expr readPtrInSrc = m_memManager.ptrAdd(b0, offset);

      Expr readFromSrc = op::bind::fapp(srcMem, readPtrInSrc);
      Expr readFromDst = op::bind::fapp(memRead, b0);

      Expr ite = boolop::lite(cmp, readFromSrc, readFromDst);
      Expr addr = bind::mkConst(mkTerm<std::string>("addr", m_efac), ptrSort);
      Expr decl = bind::fname(addr);
      res = mk<LAMBDA>(decl, ite);
      LOG("opsem.lambda", errs() << "MemCpy " << *res << "\n");
    } else {
      // no-op
      res = memRead;
    }
  } else {
    LOG("opsem.lambda", errs() << "Word size and pointer are not aligned and "
                                  "alignment is not ignored!"
                               << "\n");
    DOG(WARN << "Interpreting memcpy as noop");
    res = memRead;
  }
  return res;
}

Expr OpSemMemLambdaRepr::coerceArrayToLambda(Expr arrVal) {
  assert(bind::isArrayConst(arrVal));

  Expr name = bind::fname(arrVal);
  Expr rTy = bind::rangeTy(name);
  Expr idxTy = sort::arrayIndexTy(rTy);

  Expr bvAddr = bind::mkConst(mkTerm<std::string>("addr", m_efac), idxTy);
  Expr sel = op::array::select(arrVal, bvAddr);

  return bind::abs<LAMBDA>(as_std_array(bvAddr), sel);
}

Expr OpSemMemLambdaRepr::makeLinearITE(Expr addr, const ExprVector &ptrKeys,
                                       const ExprVector &vals, Expr fallback) {
  assert(ptrKeys.size() == vals.size());

  Expr res = fallback;

  for (size_t i = ptrKeys.size() - 1; i < ptrKeys.size(); --i) {
    Expr k = ptrKeys[i];
    Expr v = vals[i];

    Expr cmp = m_memManager.ptrEq(addr, k);
    res = boolop::lite(cmp, v, res);
  }

  return res;
}

Expr OpSemMemLambdaRepr::MemFill(Expr dPtr, char *sPtr, unsigned len, Expr mem,
                                 unsigned wordSzInBytes, Expr ptrSort,
                                 uint32_t align) {
  (void)align;
  const unsigned sem_word_sz = wordSzInBytes;
  assert(sizeof(unsigned long) >= sem_word_sz);

  Expr initial = mem;
  LOG("opsem.lambda", errs() << "MemFill init: " << *initial << "\n");

  ExprVector ptrs;
  ptrs.reserve(len);
  ExprVector vals;
  vals.reserve(len);

  for (unsigned i = 0; i < len; i += sem_word_sz) {
    // copy bytes from buffer to word - word must accommodate largest
    // supported word size
    unsigned long word = 0;
    std::memcpy(&word, sPtr + i, sem_word_sz);
    Expr val = bv::bvnum(word, wordSzInBytes * m_BitsPerByte, m_efac);

    ptrs.push_back(m_memManager.ptrAdd(dPtr, i));
    vals.push_back(val);
  }

  Expr b0 = bind::bvar(0, ptrSort);
  Expr fallback = loadAlignedWordFromMem(b0, initial);
  Expr ite = makeLinearITE(b0, ptrs, vals, fallback);
  Expr addr = bind::mkConst(mkTerm<std::string>("addr", m_efac), ptrSort);
  Expr decl = bind::fname(addr);
  Expr res = mk<LAMBDA>(decl, ite);

  LOG("opsem.lambda", errs() << "MemFill: " << *res << "\n");

  return res;
}
Expr OpSemMemLambdaRepr::FilledMemory(Expr ptrSort, Expr v) {
  Expr addr = bind::mkConst(mkTerm<std::string>("addr", m_efac), ptrSort);
  Expr decl = bind::fname(addr);
  // -- create constant lambda
  // lambda addr :: v
  return mk<LAMBDA>(decl, v);
}
} // namespace details
} // namespace seahorn
