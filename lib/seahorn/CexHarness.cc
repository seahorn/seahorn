#include "seahorn/CexHarness.hh"
#include "llvm/IR/DataLayout.h"
#include "llvm/IR/IRBuilder.h"
#include "llvm/IR/LLVMContext.h"

#include "boost/algorithm/string/replace.hpp"
#include "seahorn/Expr/ExprLlvm.hh"
#include "seahorn/Expr/ExprMemMap.hh"
#include "seahorn/Expr/ExprOpBinder.hh"
#include "seahorn/Support/SeaDebug.h"
#include "seahorn/Transforms/Instrumentation/ShadowMemDsa.hh"
#include <memory>

using namespace llvm;
namespace seahorn {

Expr BmcTraceMemSim::eval(unsigned loc, const llvm::Instruction &inst,
                          bool complete) {
  Expr v = m_mem_sim.eval(loc, inst, complete);
  LOG("cex-eval", errs() << "Eval[MemSimulator] "
                         << "loc=" << loc << " " << inst << " --> " << v
                         << "\n");
  return v;
}

Expr BmcTraceMemSim::eval(unsigned loc, Expr e, bool complete) {
  Expr v = m_mem_sim.eval(loc, e, complete);
  LOG("cex-eval", errs() << "Eval[MemSimulator] "
                         << "loc=" << loc << " " << e << " --> " << v << "\n");
  return v;
}

Constant *exprToLlvm(Type *ty, Expr e, LLVMContext &ctx, const DataLayout &dl) {
  if (isOpX<TRUE>(e)) {
    // JN: getTypeStoreSizeInBits returns 8 for i1.
    //     This causes later an error (only visible in debug mode)
    //     when calling ConstantArray::get(AT, LLVMarray) because
    //     the element type from AT will be i1 but the type of the
    //     constant in LLVMarray will be i8 because of the use of
    //     getTypeStoreSizeInBits.
    //
    // return Constant::getIntegerValue (ty,
    // APInt(dl.getTypeStoreSizeInBits(ty), 1));
    return ConstantInt::getTrue(ctx);
  } else if (isOpX<FALSE>(e)) {
    // return Constant::getNullValue (ty);
    return ConstantInt::getFalse(ctx);
  } else if (isOpX<MPZ>(e) || bv::is_bvnum(e)) {
    expr::mpz_class mpz;
    mpz = isOpX<MPZ>(e) ? getTerm<expr::mpz_class>(e)
                        : getTerm<expr::mpz_class>(e->arg(0));
    if (ty->isIntegerTy() || ty->isPointerTy()) {
      // JN: I think we can have the same issue as above but for now I leave
      // like it is.
      return Constant::getIntegerValue(
          ty, toAPInt(dl.getTypeStoreSizeInBits(ty), mpz));
    }
    llvm_unreachable("Unhandled type");
  } else {
    // HACK: in structures, first argument is usually the base value we are after
    if (strct::isStructVal(e)) {
      return exprToLlvm(ty, e->arg(0), ctx, dl);
    }
    // if all fails, try 0
    LOG("cex", WARN << "not handled value: " << *e;);
    return Constant::getNullValue(ty);
  }
  llvm_unreachable("Unhandled expression");
}

/* Given Expr of a shadow.mem segment and pre-recorded size Value
   use MemMap to extract const array with item size of current
   word size from Expr
*/
Constant *exprToMemSegment(Expr segment, Expr startAddr, Expr size,
                           llvm::LLVMContext &ctx, const llvm::DataLayout &dl) {
  if (isOp<MK_STRUCT>(segment)) {
    // first child should contain memory content
    return exprToMemSegment(segment->arg(0), startAddr, size, ctx, dl);
  }

  SmallVector<Constant *, 20> LLVMValueSegment;

  // total block size in bytes;
  expr::mpz_class sizeMpz;
  size_t blockWidth = 0;
  if (expr::numeric::getNum(size, sizeMpz)) {
    blockWidth = sizeMpz.get_ui();
  } else {
    LOG("cex",
        errs() << "memhavoc: cannot get concrete size (" << *size << ")\n");
    ArrayType *placeholderT = ArrayType::get(Type::getInt8PtrTy(ctx), 0);
    return ConstantArray::get(placeholderT, LLVMValueSegment);
  }

  // starting address
  expr::mpz_class startAddrMpz;
  size_t startAddrInt = 0;
  if (expr::numeric::getNum(startAddr, startAddrMpz)) {
    startAddrInt = startAddrMpz.get_ui();
  } else {
    LOG("cex", errs() << "memhavoc: cannot get concrete starting address: "
                      << *startAddr << "\n");
    ArrayType *placeholderT = ArrayType::get(Type::getInt8PtrTy(ctx), 0);
    return ConstantArray::get(placeholderT, LLVMValueSegment);
  }
  // use MemMap to extract mem segment info
  using MemMap = expr::exprMemMap::ExprMemMap;
  const MemMap m_map(segment);
  size_t elmWidth = m_map.getContentWidth();
  if (!m_map.isValid() || elmWidth < IntegerType::MIN_INT_BITS) {
    LOG("cex_verbose", WARN << "memhavoc: invalid memory expression: "
                            << *m_map.getRawExpr() << "\n");
    ArrayType *placeholderT = ArrayType::get(Type::getInt8PtrTy(ctx), 0);
    return ConstantArray::get(placeholderT, LLVMValueSegment);
  }
  size_t blocks = std::ceil((float)blockWidth / (float)elmWidth);
  auto *segmentElmTy = IntegerType::get(ctx, elmWidth * 8);
  ArrayType *segmentAT = ArrayType::get(segmentElmTy, blocks);

  Expr defaultE = m_map.getDefault();
  // get default value or use 0 as fallback
  Constant *defaultConst;
  if (defaultE) {
    defaultConst = exprToLlvm(segmentElmTy, defaultE, ctx, dl);
  } else {
    LOG("cex", errs() << "havocing mem with default 0 \n");
    defaultConst = Constant::getIntegerValue(
        segmentElmTy, APInt(dl.getTypeStoreSizeInBits(segmentElmTy), 0));
  }

  // fill with default values
  for (size_t i = 0; i < blocks; i++) {
    LLVMValueSegment.push_back(defaultConst);
  }

  // fill special value indicated by ID
  for (auto begin = m_map.cbegin(), end = m_map.cend(); begin != end; begin++) {
    Expr segmentID = begin->getIdxExpr();
    expr::mpz_class idE = 0;
    if (expr::numeric::getNum(segmentID, idE)) {
      size_t curAddrInt = idE.get_ui();
      size_t index = (curAddrInt - startAddrInt) / elmWidth;
      if (index >= blocks) {
        LOG("cex", errs() << "memhavoc: out of bound index: [" << index
                          << "] with only " << blocks << " blocks \n");
        continue;
      }
      Expr segmentE = begin->getValueExpr();
      auto *segmentConst = exprToLlvm(segmentElmTy, segmentE, ctx, dl);
      LLVMValueSegment[index] = segmentConst;
    } else
      continue;
  }
  return ConstantArray::get(segmentAT, LLVMValueSegment);
}
} // namespace seahorn
