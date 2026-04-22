#include "BvOpSem2MemRepr.hh"
#include "seahorn/Expr/ExprOpBinder.hh"

namespace {
template <typename T, typename... Rest>
auto as_std_array(const T &t, const Rest &...rest) ->
    typename std::array<T, sizeof...(Rest) + 1> {
  return {t, rest...};
}
} // namespace

#define DEBUG_TYPE "opsem"

namespace seahorn {
namespace details {
enum class MemSetMode { WordWise, ByteWise };

/// Classifies whether memset should use word-wise or byte-wise updates.
MemSetMode classifyMemSetMode(RawMemManagerCore &memManager,
                              unsigned wordSzInBytes, uint32_t align) {
  return (!memManager.isIgnoreAlignment() &&
          memManager.getByteAlignmentBits() != 0 && align % wordSzInBytes != 0)
             ? MemSetMode::ByteWise
             : MemSetMode::WordWise;
}

/// Builds a repeated-byte word value used by word-wise memset updates.
Expr buildMemsetWordValue(Bv2OpSemContext &ctx, ExprFactory &efac, Expr byteVal,
                          unsigned wordSzInBytes) {
  unsigned width;
  if (bv::isBvNum(byteVal, width)) {
    assert(width == 8);
    assert(wordSzInBytes <= sizeof(unsigned long));
    int byte = bv::toMpz(byteVal).get_ui();
    unsigned long word = 0;
    memset(&word, byte, wordSzInBytes);
    return bv::bvnum(word, wordSzInBytes * 8, efac);
  }

  Expr res = byteVal;
  for (unsigned i = 1; i < wordSzInBytes; ++i) {
    res = ctx.alu().Concat({byteVal, 8}, {res, 8 * i});
  }
  return res;
}

/// Rounds a symbolic byte length down to the nearest whole-word multiple.
Expr alignDownToWordSize(Bv2OpSemContext &ctx, ExprFactory &efac, Expr len,
                         unsigned ptrBitWidth, unsigned offsetBits) {
  if (offsetBits == 0) {
    return len;
  }

  Expr highBits =
      ctx.alu().Extract({len, ptrBitWidth}, offsetBits, ptrBitWidth - 1);
  return ctx.alu().Concat({highBits, ptrBitWidth - offsetBits},
                          {bv::bvnum(0U, offsetBits, efac), offsetBits});
}

/// Merges byteVal into the low bytes of oldWord for a partial-word memset tail.
Expr buildPartialMemsetWord(RawMemManagerCore &memManager, Bv2OpSemContext &ctx,
                            ExprFactory &efac, Expr oldWord, Expr byteVal,
                            Expr bytesToSet, unsigned wordSzInBytes) {
  unsigned ptrBitWidth = memManager.ptrSizeInBits();
  if (wordSzInBytes == 1) {
    Expr hasByte =
        ctx.alu().doUlt(ctx.alu().ui(0, ptrBitWidth), bytesToSet, ptrBitWidth);
    return boolop::lite(hasByte, byteVal, oldWord);
  }

  unsigned offsetBits = memManager.getByteAlignmentBits();
  Expr updatedWord = oldWord;
  for (unsigned i = 0; i < wordSzInBytes; ++i) {
    Expr inRange =
        ctx.alu().doUlt(ctx.alu().ui(i, ptrBitWidth), bytesToSet, ptrBitWidth);
    Expr nextWord = memManager.setByteOfWord(updatedWord, byteVal,
                                             bv::bvnum(i, offsetBits, efac));
    updatedWord = boolop::lite(inRange, nextWord, updatedWord);
  }
  return updatedWord;
}

/// Checks whether a specific byte address falls within the symbolic memset
/// range.
Expr isMemSetByteInRange(RawMemManagerCore &memManager,
                         RawMemManagerCore::PtrTy begin,
                         RawMemManagerCore::PtrTy bytePtr,
                         RawMemManagerCore::PtrTy end) {
  return mk<AND>(memManager.ptrUle(begin, bytePtr),
                 memManager.ptrUlt(bytePtr, end));
}

/// Checks whether the word at a byte offset is fully covered by symbolic len.
Expr isMemSetWordInRange(Bv2OpSemContext &ctx, Expr wordOffset, Expr len,
                         unsigned ptrBitWidth, unsigned wordSzInBytes) {
  Expr offsetInRange = ctx.alu().doUle(wordOffset, len, ptrBitWidth);
  Expr remainingBytes = ctx.alu().doSub(len, wordOffset, ptrBitWidth);
  Expr fullWordFits = ctx.alu().doUle(ctx.alu().ui(wordSzInBytes, ptrBitWidth),
                                      remainingBytes, ptrBitWidth);
  return mk<AND>(offsetInRange, fullWordFits);
}

/// Checks whether the word starts in range but is only partially covered.
Expr hasMemSetWordTail(Bv2OpSemContext &ctx, Expr wordOffset, Expr len,
                       unsigned ptrBitWidth, unsigned wordSzInBytes) {
  Expr fullWordCmp =
      isMemSetWordInRange(ctx, wordOffset, len, ptrBitWidth, wordSzInBytes);
  Expr startsInRange = ctx.alu().doUlt(wordOffset, len, ptrBitWidth);
  return mk<AND>(startsInRange, boolop::lneg(fullWordCmp));
}

/// Builds a lambda memory expression for aligned word-wise memset semantics.
Expr createMemSetExpr(RawMemManagerCore &memManager, Bv2OpSemContext &ctx,
                      ExprFactory &efac, RawMemManagerCore::PtrTy ptr,
                      Expr byteVal, Expr len, unsigned wordSzInBytes,
                      RawMemManagerCore::PtrSortTy ptrSort, Expr memExpr) {
  using PtrTy = RawMemManagerCore::PtrTy;

  Expr wordVal = buildMemsetWordValue(ctx, efac, byteVal, wordSzInBytes);
  PtrTy b0 = PtrTy(bind::bvar(0, ptrSort.toExpr()));
  Expr oldWord = op::bind::fapp(memExpr, b0.toExpr());

  if (wordSzInBytes == 1) {
    PtrTy end = memManager.ptrAdd(ptr, len);
    Expr inRange = isMemSetByteInRange(memManager, ptr, b0, end);
    Expr ite = boolop::lite(inRange, wordVal, oldWord);

    Expr addr =
        bind::mkConst(mkTerm<std::string>("addr", efac), ptrSort.toExpr());
    Expr decl = bind::fname(addr);
    return mk<LAMBDA>(decl, ite);
  }

  unsigned ptrBitWidth = memManager.ptrSizeInBits();
  unsigned offsetBits = memManager.getByteAlignmentBits();
  Expr alignedLen =
      alignDownToWordSize(ctx, efac, len, ptrBitWidth, offsetBits);
  Expr fullWordBytes = ctx.alu().doSub(
      alignedLen, ctx.alu().ui(wordSzInBytes, ptrBitWidth), ptrBitWidth);
  PtrTy fullWordLast = memManager.ptrAdd(ptr, fullWordBytes);
  Expr hasFullWord = ctx.alu().doUle(ctx.alu().ui(wordSzInBytes, ptrBitWidth),
                                     len, ptrBitWidth);
  Expr fullWordCmp =
      mk<AND>(hasFullWord, memManager.ptrInRangeCheck(ptr, b0, fullWordLast));

  Expr remainderBytes = ctx.alu().doSub(len, alignedLen, ptrBitWidth);
  PtrTy tailPtr = memManager.ptrAdd(ptr, alignedLen);
  Expr tailWord = buildPartialMemsetWord(
      memManager, ctx, efac, oldWord, byteVal, remainderBytes, wordSzInBytes);
  Expr hasRemainder = ctx.alu().doUlt(ctx.alu().ui(0, ptrBitWidth),
                                      remainderBytes, ptrBitWidth);
  Expr tailCmp = mk<AND>(hasRemainder, memManager.ptrEq(b0, tailPtr));

  Expr body = boolop::lite(tailCmp, tailWord, oldWord);
  body = boolop::lite(fullWordCmp, wordVal, body);

  Expr addr =
      bind::mkConst(mkTerm<std::string>("addr", efac), ptrSort.toExpr());
  Expr decl = bind::fname(addr);
  return mk<LAMBDA>(decl, body);
}

/// Builds the legacy (word-aligned) memset lambda: any address in [ptr, last]
/// gets bvVal; all others retain the old value.
static Expr createLegacyMemSetLambdaExpr(
    RawMemManagerCore &memManager, ExprFactory &efac,
    RawMemManagerCore::PtrTy ptr, Expr bvVal, Expr len, unsigned wordSzInBytes,
    RawMemManagerCore::PtrSortTy ptrSort, Expr memExpr) {
  using PtrTy = RawMemManagerCore::PtrTy;
  PtrTy last = memManager.ptrAdd(memManager.ptrAdd(ptr, len),
                                 -static_cast<signed>(wordSzInBytes));
  PtrTy b0 = PtrTy(bind::bvar(0, ptrSort.toExpr()));
  Expr cmp = memManager.ptrInRangeCheck(ptr, b0, last);
  Expr fappl = op::bind::fapp(memExpr, b0.toExpr());
  Expr ite = boolop::lite(cmp, bvVal, fappl);
  Expr addr =
      bind::mkConst(mkTerm<std::string>("addr", efac), ptrSort.toExpr());
  Expr decl = bind::fname(addr);
  return mk<LAMBDA>(decl, ite);
}

/// Applies concrete unaligned memset by updating each affected aligned word.
OpSemMemRepr::MemValTy executeConcreteUnalignedMemSet(
    OpSemMemRepr &memRepr, RawMemManagerCore &memManager, ExprFactory &efac,
    Expr byteVal, OpSemMemRepr::PtrTy ptr, unsigned len, unsigned wordSzInBytes,
    OpSemMemRepr::PtrSortTy ptrSort, OpSemMemRepr::MemValTy mem) {
  using PtrTy = OpSemMemRepr::PtrTy;

  if (len == 0) {
    return mem;
  }

  unsigned offsetBits = memManager.getByteAlignmentBits();
  PtrTy alignedBase = ptr;
  if (offsetBits != 0) {
    Expr wordAddress = memManager.ctx().alu().Extract(
        {ptr.toExpr(), memManager.ptrSizeInBits()}, offsetBits,
        memManager.ptrSizeInBits() - 1);
    alignedBase = PtrTy(memManager.ctx().alu().Concat(
        {wordAddress, memManager.ptrSizeInBits()},
        {bv::bvnum(0U, offsetBits, efac), offsetBits}));
  }

  PtrTy end = memManager.ptrAdd(ptr, len);
  auto res = mem;
  // A concrete unaligned memset can spill into one extra aligned word, so use
  // ceil((len - 1) / wordSzInBytes) + 1 to cover every touched word.
  unsigned affectedWords = ((len + wordSzInBytes - 2) / wordSzInBytes) + 1;
  for (unsigned wordIdx = 0; wordIdx < affectedWords; ++wordIdx) {
    PtrTy wordPtr = memManager.ptrAdd(alignedBase, wordIdx * wordSzInBytes);
    Expr updatedWord = memRepr.loadAlignedWordFromMem(wordPtr, res);

    for (unsigned byteIdx = 0; byteIdx < wordSzInBytes; ++byteIdx) {
      PtrTy bytePtr = memManager.ptrAdd(wordPtr, byteIdx);
      Expr inRange = isMemSetByteInRange(memManager, ptr, bytePtr, end);
      Expr nextWord = memManager.setByteOfWord(
          updatedWord, byteVal, bv::bvnum(byteIdx, offsetBits, efac));
      updatedWord = boolop::lite(inRange, nextWord, updatedWord);
    }

    res = memRepr.storeAlignedWordToMem(updatedWord, wordPtr, ptrSort, res);
  }
  return res;
}

/// Executes concrete-length memset for the array memory representation.
OpSemMemRepr::MemValTy OpSemMemArrayRepr::MemSet(PtrTy ptr, Expr _val,
                                                 unsigned len, MemValTy mem,
                                                 unsigned wordSzInBytes,
                                                 PtrSortTy ptrSort,
                                                 uint32_t align) {
  (void)ptrSort;

  if (m_memManager.isAllowPartialWordMemset()) {
    if (classifyMemSetMode(m_memManager, wordSzInBytes, align) ==
        MemSetMode::ByteWise) {
      return executeConcreteUnalignedMemSet(*this, m_memManager, m_efac, _val,
                                            ptr, len, wordSzInBytes, ptrSort,
                                            mem);
    }

    Expr res = mem.toExpr();
    Expr wordVal = buildMemsetWordValue(m_ctx, m_efac, _val, wordSzInBytes);
    unsigned fullWordBytes = len - (len % wordSzInBytes);

    for (unsigned i = 0; i < fullWordBytes; i += wordSzInBytes) {
      Expr idx = m_memManager.ptrAdd(ptr, i).toExpr();
      res = op::array::store(res, idx, wordVal);
    }

    unsigned remainderBytes = len % wordSzInBytes;
    if (remainderBytes != 0) {
      Expr idx = m_memManager.ptrAdd(ptr, fullWordBytes).toExpr();
      Expr oldWord = op::array::select(res, idx);
      Expr tailWord = buildPartialMemsetWord(
          m_memManager, m_ctx, m_efac, oldWord, _val,
          m_ctx.alu().ui(remainderBytes, m_memManager.ptrSizeInBits()),
          wordSzInBytes);
      res = op::array::store(res, idx, tailWord);
    }

    return MemValTy(res);
  }

  // MemSet operates at word level.
  // _val must fit within a byte
  // _val is converted to a byte.
  // byte is converted to a word
  // e.g. _val = 0x1, len = 0x1, wordSzInBytes = 0x4 => 0x00000001
  // e.g. _val = 0x1, len = 0x4, wordSzInBytes = 0x4 => 0x00000001
  Expr wordVal = buildMemsetWordValue(m_ctx, m_efac, _val, wordSzInBytes);
  Expr res = mem.toExpr();
  for (unsigned i = 0; i < len; i += wordSzInBytes) {
    Expr idx = m_memManager.ptrAdd(ptr, i).toExpr();
    res = op::array::store(res, idx, wordVal);
  }
  return MemValTy(res);
}

// len is in bytes
// _val must fit within a byte
/// Executes symbolic-length memset for the array memory representation.
OpSemMemRepr::MemValTy OpSemMemArrayRepr::MemSet(PtrTy ptr, Expr _val, Expr len,
                                                 MemValTy mem,
                                                 unsigned wordSzInBytes,
                                                 PtrSortTy ptrSort,
                                                 uint32_t align) {
  (void)ptrSort;

  if (m_memManager.isAllowPartialWordMemset()) {
    if (classifyMemSetMode(m_memManager, wordSzInBytes, align) ==
        MemSetMode::ByteWise) {
      // Use a simple byte-wise store loop for symbolic-length memset, if
      // unaligned
      auto res = mem;
      unsigned ptrBitWidth = m_memManager.ptrSizeInBits();
      for (unsigned i = 0; i < m_memCpyUnrollCnt; ++i) {
        Expr inRange =
            m_ctx.alu().doUlt(m_ctx.alu().ui(i, ptrBitWidth), len, ptrBitWidth);
        Expr stored = m_memManager
                          .storeIntToMem(_val, m_memManager.ptrAdd(ptr, i), res,
                                         1 /* byteSz */, 1 /* align */)
                          .toExpr();
        res = MemValTy(boolop::lite(inRange, stored, res.toExpr()));
      }
      return res;
    }

    Expr res = mem.toExpr();
    Expr wordVal = buildMemsetWordValue(m_ctx, m_efac, _val, wordSzInBytes);
    unsigned ptrBitWidth = m_memManager.ptrSizeInBits();

    // Within unroll bound, for each word decide whether
    // 1. the whole word is in range to be set to wordVal, or
    // 2. only part of the word is in range to be set to wordVal, and
    //    if so stitch the word together with old value in memory, or
    // 3. the word is out of range and should remain unchanged
    for (unsigned i = 0; i < m_memCpyUnrollCnt; i += wordSzInBytes) {
      Expr idx = m_memManager.ptrAdd(ptr, i).toExpr();
      Expr wordOffset = m_ctx.alu().ui(i, ptrBitWidth);
      Expr fullWordCmp = isMemSetWordInRange(m_ctx, wordOffset, len,
                                             ptrBitWidth, wordSzInBytes);
      Expr hasTail =
          hasMemSetWordTail(m_ctx, wordOffset, len, ptrBitWidth, wordSzInBytes);

      Expr oldWord = op::array::select(res, idx);
      Expr bytesToSet = m_ctx.alu().doSub(len, wordOffset, ptrBitWidth);
      Expr tailWord =
          buildPartialMemsetWord(m_memManager, m_ctx, m_efac, oldWord, _val,
                                 bytesToSet, wordSzInBytes);
      Expr nextWord = boolop::lite(fullWordCmp, wordVal, tailWord);
      Expr stored = op::array::store(res, idx, nextWord);
      res = boolop::lite(mk<OR>(fullWordCmp, hasTail), stored, res);
    }

    LOG("opsem.array", errs() << "memset: " << *res << "\n";);
    return MemValTy(res);
  }

  // extend _val to current word size
  Expr res;
  unsigned width;
  Expr bvVal;
  if (bv::isBvNum(_val, width)) {
    assert(width == 8);
    assert(wordSzInBytes <= sizeof(unsigned long));
    int byte = bv::toMpz(_val).get_ui();
    unsigned long val = 0;
    memset(&val, byte, wordSzInBytes);
    bvVal = bv::bvnum(val, wordSzInBytes * m_BitsPerByte, m_efac);
  } else {
    bvVal = _val;
    for (unsigned i = 1; i < wordSzInBytes; ++i)
      bvVal = m_ctx.alu().Concat({bvVal, 8}, {bvVal, 8 * i});
  }

  // write into memory
  res = mem.toExpr();
  // XXX assume that bit-width(len) == ptrSizeInBits
  auto bitWidth = m_memManager.ptrSizeInBits();
  Expr upperBound = m_ctx.alu().doAdd(
      len, m_ctx.alu().si(-static_cast<signed>(wordSzInBytes), bitWidth),
      bitWidth);
  for (unsigned i = 0; i < m_memCpyUnrollCnt; i += wordSzInBytes) {
    Expr idx = m_memManager.ptrAdd(ptr, i).toExpr();
    auto cmp =
        m_ctx.alu().doUle(m_ctx.alu().ui(i, m_memManager.ptrSizeInBits()),
                          upperBound, m_memManager.ptrSizeInBits());
    Expr ite = boolop::lite(cmp, bvVal, op::array::select(mem.toExpr(), idx));
    res = op::array::store(res, idx, ite);
  }
  LOG("opsem.array", errs() << "memset: " << *res << "\n";);
  return MemValTy(res);
}

// TODO: This function is untested
OpSemMemRepr::MemValTy OpSemMemArrayRepr::MemCpy(
    PtrTy dPtr, PtrTy sPtr, Expr len, MemValTy memTrsfrRead, MemValTy memRead,
    unsigned wordSzInBytes, PtrSortTy ptrSort, uint32_t align) {
  (void)ptrSort;
  Expr res = memRead.toExpr();
  Expr srcMem = memTrsfrRead.toExpr();
  if (wordSzInBytes == 1 || (wordSzInBytes == 4 && align % 4 == 0) ||
      (wordSzInBytes == 8 && align % 4 == 0) ||
      m_memManager.isIgnoreAlignment()) {
    // XXX assume that bit-width(len) == ptrSizeInBits
    auto bitWidth = m_memManager.ptrSizeInBits();
    Expr upperBound = m_ctx.alu().doAdd(
        len, m_ctx.alu().si(-static_cast<signed>(wordSzInBytes), bitWidth),
        bitWidth);
    for (unsigned i = 0; i < m_memCpyUnrollCnt; i += wordSzInBytes) {
      Expr dIdx = m_memManager.ptrAdd(dPtr, i).toExpr();
      Expr sIdx = m_memManager.ptrAdd(sPtr, i).toExpr();
      auto cmp =
          m_ctx.alu().doUle(m_ctx.alu().ui(i, m_memManager.ptrSizeInBits()),
                            upperBound, m_memManager.ptrSizeInBits());
      auto ite = boolop::lite(cmp, op::array::select(srcMem, sIdx),
                              op::array::select(memRead.toExpr(), dIdx));
      res = op::array::store(res, dIdx, ite);
    }
    LOG("opsem.array", INFO << "memcpy: " << *res << "\n";);

  } else {
    DOG(ERR << "Word size and pointer are not aligned and "
               "alignment is not ignored!");
    DOG(ERR << "Try --horn-bv2-lambdas=true or --horn-bv2-word-size=1");
    assert(false);
  }
  return MemValTy(res);
}

OpSemMemRepr::MemValTy
OpSemMemArrayRepr::MemCpy(PtrTy dPtr, PtrTy sPtr, unsigned len,
                          MemValTy memTrsfrRead, MemValTy memRead,
                          unsigned wordSzInBytes, PtrSortTy ptrSort,
                          uint32_t align) {
  (void)ptrSort;

  Expr res;

  if (wordSzInBytes == 1 || (wordSzInBytes == 4 && align % 4 == 0) ||
      (wordSzInBytes == 8 && align % 4 == 0) ||
      m_memManager.isIgnoreAlignment()) {
    Expr srcMem = memTrsfrRead.toExpr();
    res = memRead.toExpr();
    for (unsigned i = 0; i < len; i += wordSzInBytes) {
      Expr dIdx = m_memManager.ptrAdd(dPtr, i).toExpr();
      Expr sIdx = m_memManager.ptrAdd(sPtr, i).toExpr();

      Expr val = op::array::select(srcMem, sIdx);
      res = op::array::store(res, dIdx, val);
    }
  } else {
    DOG(ERR << "Word size and pointer are not aligned and "
               "alignment is not ignored!"
            << "\n");
    assert(false);
  }
  return MemValTy(res);
}

OpSemMemRepr::MemValTy OpSemMemArrayRepr::MemFill(PtrTy dPtr, char *sPtr,
                                                  unsigned len, MemValTy mem,
                                                  unsigned wordSzInBytes,
                                                  PtrSortTy ptrSort,
                                                  uint32_t align) {
  Expr res = mem.toExpr();
  const unsigned sem_word_sz = wordSzInBytes;

  // 8 bytes because assumed largest supported sem_word_sz = 8
  assert(sizeof(unsigned long) >= sem_word_sz);

  for (unsigned i = 0; i < len; i += sem_word_sz) {
    Expr dIdx = m_memManager.ptrAdd(dPtr, i).toExpr();
    // copy bytes from buffer to word - word must accommodate largest
    // supported word size
    // 8 bytes because assumed largest supported sem_word_sz = 8
    unsigned long word = 0;
    std::memcpy(&word, sPtr + i, sem_word_sz);
    Expr val = bv::bvnum(word, wordSzInBytes * m_BitsPerByte, m_efac);
    res = op::array::store(res, dIdx, val);
  }
  return MemValTy(res);
}

OpSemMemRepr::MemValTy
OpSemMemLambdaRepr::storeAlignedWordToMem(Expr val, PtrTy ptr,
                                          PtrSortTy ptrSort, MemValTy mem) {
  PtrTy b0 = PtrTy(bind::bvar(0, ptrSort.toExpr()));

  Expr fappl = op::bind::fapp(mem.toExpr(), b0.toExpr());
  Expr ite = boolop::lite(m_memManager.ptrEq(b0, ptr), val, fappl);

  Expr addr =
      bind::mkConst(mkTerm<std::string>("addr", m_efac), ptrSort.toExpr());
  Expr decl = bind::fname(addr);
  return MemValTy(mk<LAMBDA>(decl, ite));
}

// len is in bytes
/// Executes concrete-length memset for the lambda memory representation.
OpSemMemRepr::MemValTy OpSemMemLambdaRepr::MemSet(PtrTy ptr, Expr _val,
                                                  unsigned len, MemValTy mem,
                                                  unsigned wordSzInBytes,
                                                  PtrSortTy ptrSort,
                                                  uint32_t align) {
  if (m_memManager.isAllowPartialWordMemset()) {
    if (classifyMemSetMode(m_memManager, wordSzInBytes, align) ==
        MemSetMode::ByteWise) {
      return executeConcreteUnalignedMemSet(*this, m_memManager, m_efac, _val,
                                            ptr, len, wordSzInBytes, ptrSort,
                                            mem);
    }

    Expr res =
        createMemSetExpr(m_memManager, m_ctx, m_efac, ptr, _val,
                         m_ctx.alu().ui(len, m_memManager.ptrSizeInBits()),
                         wordSzInBytes, ptrSort, mem.toExpr());
    LOG("opsem.lambda", errs() << "MemSet " << *res << "\n");
    return MemValTy(res);
  }

  Expr bvVal = buildMemsetWordValue(m_ctx, m_efac, _val, wordSzInBytes);
  Expr res = createLegacyMemSetLambdaExpr(
      m_memManager, m_efac, ptr, bvVal,
      m_ctx.alu().ui(len, m_memManager.ptrSizeInBits()), wordSzInBytes, ptrSort,
      mem.toExpr());
  LOG("opsem.lambda", errs() << "MemSet " << *res << "\n");
  return MemValTy(res);
}

/// Executes symbolic-length memset for the lambda memory representation.
OpSemMemRepr::MemValTy OpSemMemLambdaRepr::MemSet(PtrTy ptr, Expr _val,
                                                  Expr len, MemValTy mem,
                                                  unsigned wordSzInBytes,
                                                  PtrSortTy ptrSort,
                                                  uint32_t align) {
  if (m_memManager.isAllowPartialWordMemset()) {
    if (classifyMemSetMode(m_memManager, wordSzInBytes, align) ==
        MemSetMode::ByteWise) {
      unsigned offsetBits = m_memManager.getByteAlignmentBits();

      PtrTy b0 = PtrTy(bind::bvar(0, ptrSort.toExpr()));
      Expr oldWord = op::bind::fapp(mem.toExpr(), b0.toExpr());
      PtrTy end = m_memManager.ptrAdd(ptr, len);

      Expr updatedWord = oldWord;
      for (unsigned i = 0; i < wordSzInBytes; ++i) {
        PtrTy bytePtr = m_memManager.ptrAdd(b0, i);
        Expr inRange = isMemSetByteInRange(m_memManager, ptr, bytePtr, end);
        Expr nextWord = m_memManager.setByteOfWord(
            updatedWord, _val, bv::bvnum(i, offsetBits, m_efac));
        updatedWord = boolop::lite(inRange, nextWord, updatedWord);
      }

      Expr addr =
          bind::mkConst(mkTerm<std::string>("addr", m_efac), ptrSort.toExpr());
      Expr decl = bind::fname(addr);
      Expr res = mk<LAMBDA>(decl, updatedWord);
      LOG("opsem.lambda", errs() << "MemSet " << *res << "\n");
      return MemValTy(res);
    }

    Expr res = createMemSetExpr(m_memManager, m_ctx, m_efac, ptr, _val, len,
                                wordSzInBytes, ptrSort, mem.toExpr());
    LOG("opsem.lambda", errs() << "MemSet " << *res << "\n");
    return MemValTy(res);
  }

  DOG(if (wordSzInBytes != 1) WARN << "memset: untested word size: "
                                   << wordSzInBytes);
  Expr bvVal = buildMemsetWordValue(m_ctx, m_efac, _val, wordSzInBytes);
  Expr res = createLegacyMemSetLambdaExpr(m_memManager, m_efac, ptr, bvVal, len,
                                          wordSzInBytes, ptrSort, mem.toExpr());
  LOG("opsem.lambda", errs() << "MemSet " << *res << "\n");
  return MemValTy(res);
}

OpSemMemRepr::MemValTy OpSemMemLambdaRepr::MemCpy(
    PtrTy dPtr, PtrTy sPtr, Expr len, MemValTy memTrsfrRead, MemValTy memRead,
    unsigned wordSzInBytes, PtrSortTy ptrSort, uint32_t align) {
  MemValTy srcMem = memTrsfrRead;
  // address of the last word that is copied into dst
  PtrTy dstLast = m_memManager.ptrAdd(m_memManager.ptrAdd(dPtr, len),
                                      -static_cast<signed>(wordSzInBytes));
  return createMemCpyExpr(dPtr, sPtr, memRead, ptrSort, srcMem, dstLast,
                          wordSzInBytes, align);
}

// TODO: Call this from concrete LambdaRepr::MemCpy also to
// remove duplicate code
OpSemMemRepr::MemValTy OpSemMemLambdaRepr::createMemCpyExpr(
    const PtrTy &dPtr, const PtrTy &sPtr, const MemValTy &memRead,
    const PtrSortTy &ptrSort, const MemValTy &srcMem, const PtrTy &dstLast,
    unsigned wordSzInBytes, uint32_t align) const {
  MemValTy res = MemValTy(Expr());
  if (wordSzInBytes == 1 || (wordSzInBytes == 4 && align % 4 == 0) ||
      (wordSzInBytes == 8 && align % 4 == 0) ||
      m_memManager.isIgnoreAlignment()) {
    PtrTy b0 = PtrTy(bind::bvar(0, ptrSort.toExpr()));
    // -- dPtr <= b0 <= dstLast
    Expr cmp = this->m_memManager.ptrInRangeCheck(dPtr, b0, dstLast);
    // -- offset == dPtr - sPtr
    Expr offset = this->m_memManager.ptrOffsetFromBase(dPtr, sPtr);
    // -- maps ptr in dst to ptr in src
    Expr readPtrInSrc = this->m_memManager.ptrAdd(b0, offset).toExpr();

    Expr readFromSrc = bind::fapp(srcMem.toExpr(), readPtrInSrc);
    Expr readFromDst = bind::fapp(memRead.toExpr(), b0.toExpr());

    Expr ite = boolop::lite(cmp, readFromSrc, readFromDst);
    Expr addr = bind::mkConst(mkTerm<std::string>("addr", this->m_efac),
                              ptrSort.toExpr());
    Expr decl = bind::fname(addr);
    res = MemValTy(mk<LAMBDA>(decl, ite));
    LOG("opsem.lambda", errs() << "MemCpy " << *res.v() << "\n");
  } else {
    DOG(ERR << "unsupported memcpy due to size and/or alignment.";);
    DOG(WARN << "Interpreting memcpy as noop");
    res = memRead;
  }
  return res;
}

OpSemMemRepr::MemValTy
OpSemMemLambdaRepr::MemCpy(PtrTy dPtr, PtrTy sPtr, unsigned len,
                           MemValTy memTrsfrRead, MemValTy memRead,
                           unsigned wordSzInBytes, PtrSortTy ptrSort,
                           uint32_t align) {
  MemValTy res = MemValTy(Expr());

  if (wordSzInBytes == 1 || (wordSzInBytes == 4 && align % 4 == 0) ||
      (wordSzInBytes == 8 && align % 4 == 0) ||
      m_memManager.isIgnoreAlignment()) {
    MemValTy srcMem = memTrsfrRead;

    if (len > 0) {
      unsigned lastAlignedBytePosToCopy;
      unsigned remainderBytes;
      if (m_memManager.isIgnoreAlignment()) {
        // if alignment is ignored, we treat it as alignment of 1
        lastAlignedBytePosToCopy = len - 1;
        remainderBytes = 0;
      } else {
        unsigned wordsToCopy = (len / wordSzInBytes);
        // -- -1 because ptrInRangeCheck is inclusive
        lastAlignedBytePosToCopy = (wordsToCopy - 1) * wordSzInBytes;
        remainderBytes = len % wordSzInBytes;
      }

      PtrTy dstLast = m_memManager.ptrAdd(dPtr, lastAlignedBytePosToCopy);

      PtrTy b0 = PtrTy(bind::bvar(0, ptrSort.toExpr()));
      Expr cmp = m_memManager.ptrInRangeCheck(dPtr, b0, dstLast);
      Expr offset = m_memManager.ptrOffsetFromBase(dPtr, sPtr);
      PtrTy readPtrInSrc = m_memManager.ptrAdd(b0, offset);

      Expr readFromSrc = op::bind::fapp(srcMem.toExpr(), readPtrInSrc.toExpr());
      Expr readFromDst = op::bind::fapp(memRead.toExpr(), b0.toExpr());

      // -- body of the new lambda function
      Expr body;
      if (remainderBytes) {
        LOG("opsem.lambda",
            WARN << "memcpy of incomplete words. potential bottleneck.");
        // -- if there are remainder bytes, stitch the last word together

        // -- address of last word in destination is after the last word copied
        PtrTy lastWordAddr =
            m_memManager.ptrAdd(dPtr, lastAlignedBytePosToCopy + wordSzInBytes);
        Expr isLastWordCmp = m_memManager.ptrEq(b0, lastWordAddr);

        // -- after compare, B0 is the same as last address
        Expr lastWordValDst = op::bind::fapp(memRead.toExpr(), b0.toExpr());
        // -- readPtrInSrc is an address in src that is at the corresponding
        // offset from B0
        Expr lastWordValSrc =
            op::bind::fapp(srcMem.toExpr(), readPtrInSrc.toExpr());

        // -- compute the last word by taking chunks of source and destination
        // -- words. source word comes first
        unsigned wordSzInBits = wordSzInBytes * 8;
        unsigned remainderBits = remainderBytes * 8;
        auto &alu = m_ctx.alu();
        Expr srcChunk =
            alu.Extract({lastWordValSrc, wordSzInBits}, 0, remainderBits - 1);
        Expr dstChunk = alu.Extract({lastWordValDst, wordSzInBits},
                                    remainderBits, wordSzInBits - 1);
        Expr lastWordVal = alu.Concat({dstChunk, wordSzInBits - remainderBits},
                                      {srcChunk, remainderBits});

        // -- construct the big ITE
        body = boolop::lite(isLastWordCmp, lastWordVal, readFromDst);
        body = boolop::lite(cmp, readFromSrc, body);
      } else {
        body = boolop::lite(cmp, readFromSrc, readFromDst);
      }

      // -- create lambda function by binding B0 to be the function argument
      Expr addr =
          bind::mkConst(mkTerm<std::string>("addr", m_efac), ptrSort.toExpr());
      Expr decl = bind::fname(addr);
      res = MemValTy(mk<LAMBDA>(decl, body));
      LOG("opsem.lambda", errs() << "MemCpy " << *res.v() << "\n");
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

Expr OpSemMemLambdaRepr::makeLinearITE(PtrTy addr,
                                       const std::vector<PtrTy> &ptrKeys,
                                       const ExprVector &vals, Expr fallback) {
  assert(ptrKeys.size() == vals.size());

  Expr res = fallback;

  for (size_t i = ptrKeys.size() - 1; i < ptrKeys.size(); --i) {
    PtrTy k = ptrKeys[i];
    Expr v = vals[i];

    Expr cmp = m_memManager.ptrEq(addr, k);
    res = boolop::lite(cmp, v, res);
  }

  return res;
}

OpSemMemRepr::MemValTy OpSemMemLambdaRepr::MemFill(PtrTy dPtr, char *sPtr,
                                                   unsigned len, MemValTy mem,
                                                   unsigned wordSzInBytes,
                                                   PtrSortTy ptrSort,
                                                   uint32_t align) {
  (void)align;
  const unsigned sem_word_sz = wordSzInBytes;
  assert(sizeof(unsigned long) >= sem_word_sz);

  MemValTy initial = mem;
  LOG("opsem.lambda", errs() << "MemFill init: " << &initial << "\n");

  std::vector<PtrTy> ptrs;
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

  PtrTy b0 = PtrTy(bind::bvar(0, ptrSort.toExpr()));
  Expr fallback = loadAlignedWordFromMem(b0, initial);
  Expr ite = makeLinearITE(b0, ptrs, vals, fallback);
  Expr addr =
      bind::mkConst(mkTerm<std::string>("addr", m_efac), ptrSort.toExpr());
  Expr decl = bind::fname(addr);
  Expr res = mk<LAMBDA>(decl, ite);

  LOG("opsem.lambda", errs() << "MemFill: " << *res << "\n");

  return MemValTy(res);
}
OpSemMemRepr::MemValTy OpSemMemLambdaRepr::FilledMemory(PtrSortTy ptrSort,
                                                        Expr v) {
  Expr addr =
      bind::mkConst(mkTerm<std::string>("addr", m_efac), ptrSort.toExpr());
  Expr decl = bind::fname(addr);
  // -- create constant lambda
  // lambda addr :: v
  return MemValTy(mk<LAMBDA>(decl, v));
}
} // namespace details
} // namespace seahorn
