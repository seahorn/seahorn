#include "BvOpSem2Context.hh"

#include "llvm/Support/Format.h"

#include "seahorn/Expr/ExprLlvm.hh"
#include "seahorn/Support/SeaDebug.h"
#include "seahorn/Support/SeaLog.hh"

namespace seahorn {
namespace details {
OpSemAlu::OpSemAlu(Bv2OpSemContext &ctx) : m_ctx(ctx) {}

class BvOpSemAlu : public OpSemAlu {
  Expr m_trueE;
  Expr m_falseE;
  Expr m_trueBv1;
  Expr m_falseBv1;

public:
  BvOpSemAlu(Bv2OpSemContext &ctx) : OpSemAlu(ctx) {
    m_trueE = mk<TRUE>(efac());
    m_falseE = mk<FALSE>(efac());
    m_trueBv1 = bv::bvnum(1U, 1, efac());
    m_falseBv1 = bv::bvnum(0U, 1, efac());
  }
  ~BvOpSemAlu() override = default;

  Expr intTy(unsigned bitWidth) override {
    return bitWidth == 1 ? boolTy() : bv::bvsort(bitWidth, efac());
  }

  Expr boolTy() override { return sort::boolTy(efac()); }

  bool isNum(Expr v) override { return bv::isBvNum(v); }
  bool isNum(Expr v, unsigned &bitWidth) { return bv::isBvNum(v, bitWidth); }
  expr::mpz_class toNum(Expr v) override { return bv::toMpz(v); }

  Expr si(int v, unsigned bitWidth) override {
    switch (bitWidth) {
    case 1:
      return v == 1 ? m_trueE : m_falseE;
    default:
      return v < 0 ? si(expr::mpz_class(-v).neg(), bitWidth)
                   : si(expr::mpz_class(v), bitWidth);
    }
  }

  /// \brief Converts a signed integer to an ALU expression
  Expr si(expr::mpz_class v, unsigned bitWidth) override {
    switch (bitWidth) {
    case 1:
      return v == 1U ? m_trueE : m_falseE;
    default:
      return bv::bvnum(v, bitWidth, efac());
    }
  }
  Expr doAdd(Expr op0, Expr op1, unsigned bitWidth) override {
    return mk<BADD>(op0, op1);
  }
  Expr doSub(Expr op0, Expr op1, unsigned bitWidth) override {
    return mk<BSUB>(op0, op1);
  }
  Expr doMul(Expr op0, Expr op1, unsigned bitWidth) override {
    return mk<BMUL>(op0, op1);
  }
  Expr doUDiv(Expr op0, Expr op1, unsigned bitWidth) override {
    return mk<BUDIV>(op0, op1);
  }
  Expr doSDiv(Expr op0, Expr op1, unsigned bitWidth) override {
    return mk<BSDIV>(op0, op1);
  }
  Expr doURem(Expr op0, Expr op1, unsigned bitWidth) override {
    return mk<BUREM>(op0, op1);
  }
  Expr doSRem(Expr op0, Expr op1, unsigned bitWidth) override {
    return mk<BSREM>(op0, op1);
  }

  Expr doAnd(Expr op0, Expr op1, unsigned bitWidth) override {
    return bitWidth == 1 ? mk<AND>(op0, op1) : mk<BAND>(op0, op1);
  }
  Expr doOr(Expr op0, Expr op1, unsigned bitWidth) override {
    return bitWidth == 1 ? mk<OR>(op0, op1) : mk<BOR>(op0, op1);
  }
  Expr doXor(Expr op0, Expr op1, unsigned bitWidth) override {
    return bitWidth == 1 ? mk<XOR>(op0, op1) : mk<BXOR>(op0, op1);
  }

  Expr doEq(Expr op0, Expr op1, unsigned bitWidth) override {
    return mk<EQ>(op0, op1);
  }
  Expr doNe(Expr op0, Expr op1, unsigned bitWidth) override {
    return mk<NEQ>(op0, op1);
  }
  Expr doUlt(Expr op0, Expr op1, unsigned bitWidth) override {
    return mk<BULT>(op0, op1);
  }
  Expr doSlt(Expr op0, Expr op1, unsigned bitWidth) override {
    return mk<BSLT>(op0, op1);
  }
  Expr doUgt(Expr op0, Expr op1, unsigned bitWidth) override {
    return mk<BUGT>(op0, op1);
  }
  Expr doSgt(Expr op0, Expr op1, unsigned bitWidth) override {
    switch (bitWidth) {
    case 1:
      if (isOpX<TRUE>(op1))
        // icmp sgt op0, i1 true  == !op0
        return boolop::lneg(op0);
      return bv1ToBool(mk<BSGT>(boolToBv1(op0), boolToBv1(op1)));
    default:
      return mk<BSGT>(op0, op1);
    }
  }
  Expr doUle(Expr op0, Expr op1, unsigned bitWidth) override {
    return mk<BULE>(op0, op1);
  }
  Expr doSle(Expr op0, Expr op1, unsigned bitWidth) override {
    return mk<BSLE>(op0, op1);
  }
  Expr doUge(Expr op0, Expr op1, unsigned bitWidth) override {
    return mk<BUGE>(op0, op1);
  }
  Expr doSge(Expr op0, Expr op1, unsigned bitWidth) override {
    return mk<BSGE>(op0, op1);
  }

  Expr doTrunc(Expr op, unsigned bitWidth) override {
    Expr res = bv::extract(bitWidth - 1, 0, op);
    return bitWidth == 1 ? bv1ToBool(res) : res;
  }

  Expr doZext(Expr op, unsigned bitWidth, unsigned opBitWidth) override {
    Expr res = op;
    switch (opBitWidth) {
    case 1:
      if (isOpX<TRUE>(op))
        return si(1U, bitWidth);
      else if (isOpX<FALSE>(op))
        return si(0U, bitWidth);
      return mk<ITE>(op, si(1U, bitWidth), si(0U, bitWidth));
    default:
      return bv::zext(op, bitWidth);
    }
  }

  Expr doSext(Expr op, unsigned bitWidth, unsigned opBitWidth) override {
    Expr res = op;
    if (opBitWidth == 1)
      op = boolToBv1(op);
    return bv::sext(op, bitWidth);
  }

  Expr Extract(std::pair<Expr, unsigned int> op, unsigned begin, unsigned end) {
    Expr res = bv::extract(end, begin, op.first);
    return (end == begin) ? bv1ToBool(res) : res;
  }

  Expr Concat(std::pair<Expr, unsigned int> opHigh,
              std::pair<Expr, unsigned int> opLow) {
    Expr opHighBv = opHigh.second == 1 ? boolToBv1(opHigh.first) : opHigh.first;
    Expr opLowBv = opLow.second == 1 ? boolToBv1(opLow.first) : opLow.first;
    return bv::concat(opHighBv, opLowBv);
  }

  Expr IsSaddNoOverflow(Expr op0, Expr op1, unsigned bitWidth) {
    return mk<SADD_NO_OVERFLOW>(op0, op1);
  }

  Expr IsBaddNoUnderflow(Expr op0, Expr op1, unsigned bidWidth) {
    return mk<SADD_NO_UNDERFLOW>(op0, op1);
  }

  Expr IsUaddNoOverflow(Expr op0, Expr op1, unsigned bidWidth) {
    return mk<UADD_NO_OVERFLOW>(op0, op1);
  }

  Expr IsBsubNoOverflow(Expr op0, Expr op1, unsigned bitWidth) {
    return mk<SSUB_NO_OVERFLOW>(op0, op1);
  }

  Expr IsSsubNoUnderflow(Expr op0, Expr op1, unsigned bidWidth) {
    return mk<SSUB_NO_UNDERFLOW>(op0, op1);
  }

  Expr IsUsubNoUnderflow(Expr op0, Expr op1, unsigned bidWidth) {
    return mk<USUB_NO_UNDERFLOW>(op0, op1);
  }

  Expr IsSmulNoOverflow(Expr op0, Expr op1, unsigned bidWidth) {
    return mk<SMUL_NO_OVERFLOW>(op0, op1);
  }

  Expr IsUmulNoOverflow(Expr op0, Expr op1, unsigned bidWidth) {
    return mk<UMUL_NO_OVERFLOW>(op0, op1);
  }

  Expr IsBmulNoUnderflow(Expr op0, Expr op1, unsigned bidWidth) {
    return mk<SMUL_NO_UNDERFLOW>(op0, op1);
  }

  Expr doNot(Expr op0, unsigned bitWidth) {
    return bitWidth == 1 ? mk<NEG>(op0) : bv::bvnot(op0);
  }

  Expr boolToBv1(Expr b) {
    if (isOpX<TRUE>(b))
      return m_trueBv1;
    if (isOpX<FALSE>(b))
      return m_falseBv1;
    return mk<ITE>(b, m_trueBv1, m_falseBv1);
  }

  Expr bv1ToBool(Expr bv) {
    if (bv == m_trueBv1)
      return m_trueE;
    if (bv == m_falseBv1)
      return m_falseE;
    return mk<EQ>(bv, m_trueBv1);
  }

  Expr getFalse() { return m_falseE; }

  Expr getTrue() { return m_trueE; }
};

std::unique_ptr<OpSemAlu> mkBvOpSemAlu(Bv2OpSemContext &ctx) {
  return std::make_unique<BvOpSemAlu>(ctx);
}
} // namespace details
} // namespace seahorn
