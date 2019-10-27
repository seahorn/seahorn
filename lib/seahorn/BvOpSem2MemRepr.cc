#include "BvOpSem2Context.hh"
#include "seahorn/Expr/ExprOpBinder.hh"
namespace {
template <typename T, typename... Rest>
auto as_std_array(const T &t, const Rest &... rest) ->
    typename std::array<T, sizeof...(Rest) + 1> {
  return {t, rest...};
}
} // namespace

namespace seahorn {
namespace details {

Expr OpSemMemArrayRepr::MemSet(Expr ptr, Expr _val, unsigned len,
                               Expr memReadReg, Expr memWriteReg,
                               unsigned wordSzInBytes, Expr ptrSort,
                               uint32_t align) {
  Expr res;

  unsigned width;
  if (bv::isBvNum(_val, width) && width == 8) {
    assert(wordSzInBytes <= sizeof(unsigned long));
    int byte = bv::toMpz(_val).get_ui();
    unsigned long val = 0;
    memset(&val, byte, wordSzInBytes);

    res = m_ctx.read(memReadReg);
    for (unsigned i = 0; i < len; i += wordSzInBytes) {
      Expr idx = m_memManager.ptrAdd(ptr, i);
      res = op::array::store(
          res, idx, bv::bvnum(val, wordSzInBytes * m_BitsPerByte, m_efac));
    }
    m_ctx.write(memWriteReg, res);
  }

  return res;
}

Expr OpSemMemArrayRepr::MemCpy(Expr dPtr, Expr sPtr, unsigned len,
                               Expr memTrsfrReadReg, Expr memReadReg,
                               Expr memWriteReg, unsigned wordSzInBytes,
                               Expr ptrSort, uint32_t align) {
  (void)memReadReg, ptrSort;

  Expr res;

  if (wordSzInBytes == 1 || (wordSzInBytes == 4 && align == 4)) {
    Expr srcMem = m_ctx.read(memTrsfrReadReg);
    res = srcMem;
    for (unsigned i = 0; i < len; i += wordSzInBytes) {
      Expr dIdx = m_memManager.ptrAdd(dPtr, i);
      Expr sIdx = m_memManager.ptrAdd(sPtr, i);

      Expr val = op::array::select(srcMem, sIdx);
      res = op::array::store(res, dIdx, val);
    }
    m_ctx.write(memWriteReg, res);
  }
  return res;
}

Expr OpSemMemArrayRepr::MemFill(Expr dPtr, char *sPtr, unsigned len,
                                unsigned wordSzInBytes, Expr ptrSort,
                                uint32_t align) {
  Expr res = m_ctx.read(m_ctx.getMemReadRegister());
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
  m_ctx.write(m_ctx.getMemWriteRegister(), res);
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

Expr OpSemMemLambdaRepr::MemSet(Expr ptr, Expr _val, unsigned len,
                                Expr memReadReg, Expr memWriteReg,
                                unsigned wordSzInBytes, Expr ptrSort,
                                uint32_t align) {
  Expr res;

  unsigned width;
  if (bv::isBvNum(_val, width) && width == 8) {
    assert(wordSzInBytes <= sizeof(unsigned long));
    int byte = bv::toMpz(_val).get_ui();
    unsigned long val = 0;
    memset(&val, byte, wordSzInBytes);

    res = m_ctx.read(memReadReg);

    Expr last = m_memManager.ptrAdd(ptr, len - wordSzInBytes);
    Expr bvVal = bv::bvnum(val, wordSzInBytes * m_BitsPerByte, m_efac);
    Expr b0 = bind::bvar(0, ptrSort);

    Expr cmp = m_memManager.ptrInRangeCheck(ptr, b0, last);
    Expr fappl = op::bind::fapp(res, b0);
    Expr ite = boolop::lite(cmp, bvVal, fappl);

    Expr addr = bind::mkConst(mkTerm<std::string>("addr", m_efac), ptrSort);
    Expr decl = bind::fname(addr);
    res = mk<LAMBDA>(decl, ite);
    LOG("opsem.lambda", errs() << "MemSet " << *res << "\n");

    m_ctx.write(memWriteReg, res);
  }

  return res;
}

Expr OpSemMemLambdaRepr::MemCpy(Expr dPtr, Expr sPtr, unsigned len,
                                Expr memTrsfrReadReg, Expr memReadReg,
                                Expr memWriteReg, unsigned wordSzInBytes,
                                Expr ptrSort, uint32_t align) {
  Expr res;

  if (wordSzInBytes == 1 || (wordSzInBytes == 4 && align == 4)) {
    Expr srcMem = m_ctx.read(memTrsfrReadReg);

    if (len > 0) {
      unsigned bytesToCpy = len - wordSzInBytes;
      Expr dstLast = m_memManager.ptrAdd(dPtr, bytesToCpy);

      Expr b0 = bind::bvar(0, ptrSort);
      Expr cmp = m_memManager.ptrInRangeCheck(dPtr, b0, dstLast);
      Expr offset = m_memManager.ptrOffsetFromBase(dPtr, sPtr);
      Expr readPtrInSrc = m_memManager.ptrAdd(b0, offset);

      // Both reads are from the same memory but must not overlap.
      Expr readFromSrc = op::bind::fapp(srcMem, readPtrInSrc);
      Expr readFromDst = op::bind::fapp(srcMem, b0);

      Expr ite = boolop::lite(cmp, readFromSrc, readFromDst);
      Expr addr = bind::mkConst(mkTerm<std::string>("addr", m_efac), ptrSort);
      Expr decl = bind::fname(addr);
      res = mk<LAMBDA>(decl, ite);
      LOG("opsem.lambda", errs() << "MemCpy " << *res << "\n");
    }

    m_ctx.write(memWriteReg, res);
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

Expr OpSemMemLambdaRepr::MemFill(Expr dPtr, char *sPtr, unsigned len,
                                 unsigned wordSzInBytes, Expr ptrSort,
                                 uint32_t align) {
  (void)align;
  const unsigned sem_word_sz = wordSzInBytes;
  assert(sizeof(unsigned long) >= sem_word_sz);

  Expr initial = m_ctx.read(m_ctx.getMemReadRegister());
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

  m_ctx.write(m_ctx.getMemWriteRegister(), res);
  return res;
}

} // namespace details
} // namespace seahorn
