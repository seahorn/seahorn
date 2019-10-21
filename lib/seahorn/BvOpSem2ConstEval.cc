#include "BvOpSem2Context.hh"

#include "seahorn/Expr/ExprLlvm.hh"
#include "llvm/Support/Format.h"
using namespace llvm;

namespace seahorn {
namespace details {

/// Adapted from llvm::ExecutionEngine::getConstantValue
Optional<GenericValue> ConstantExprEvaluator::evaluate(const Constant *C) {
  // If its undefined, return the garbage.
  if (isa<UndefValue>(C)) {
    GenericValue Result;
    switch (C->getType()->getTypeID()) {
    default:
      break;
    case Type::IntegerTyID:
    case Type::X86_FP80TyID:
    case Type::FP128TyID:
    case Type::PPC_FP128TyID:
      // Although the value is undefined, we still have to construct an APInt
      // with the correct bit width.
      Result.IntVal = APInt(C->getType()->getPrimitiveSizeInBits(), 0);
      break;
    case Type::StructTyID: {
      // if the whole struct is 'undef' just reserve memory for the value.
      if (StructType *STy = dyn_cast<StructType>(C->getType())) {
        unsigned int elemNum = STy->getNumElements();
        Result.AggregateVal.resize(elemNum);
        for (unsigned int i = 0; i < elemNum; ++i) {
          Type *ElemTy = STy->getElementType(i);
          if (ElemTy->isIntegerTy())
            Result.AggregateVal[i].IntVal =
                APInt(ElemTy->getPrimitiveSizeInBits(), 0);
          else if (ElemTy->isAggregateType()) {
            const Constant *ElemUndef = UndefValue::get(ElemTy);
            Result.AggregateVal[i] = evaluate(ElemUndef).getValue();
          }
        }
      }
    } break;
    case Type::VectorTyID:
      // if the whole vector is 'undef' just reserve memory for the value.
      auto *VTy = dyn_cast<VectorType>(C->getType());
      Type *ElemTy = VTy->getElementType();
      unsigned int elemNum = VTy->getNumElements();
      Result.AggregateVal.resize(elemNum);
      if (ElemTy->isIntegerTy())
        for (unsigned int i = 0; i < elemNum; ++i)
          Result.AggregateVal[i].IntVal =
              APInt(ElemTy->getPrimitiveSizeInBits(), 0);
      break;
    }
    return Result;
  }

  // Otherwise, if the value is a ConstantExpr...
  if (const ConstantExpr *CE = dyn_cast<ConstantExpr>(C)) {
    Constant *Op0 = CE->getOperand(0);
    switch (CE->getOpcode()) {
    case Instruction::GetElementPtr: {
      // Compute the index
      auto base = evaluate(Op0);
      GenericValue Result = base.getValue();
      APInt Offset(getDataLayout().getPointerSizeInBits(), 0);
      cast<GEPOperator>(CE)->accumulateConstantOffset(getDataLayout(), Offset);

      char *tmp = (char *)Result.PointerVal;
      Result = PTOGV(tmp + Offset.getSExtValue());
      return Result;
    }
    case Instruction::Trunc: {
      GenericValue GV = evaluate(Op0).getValue();
      uint32_t BitWidth = cast<IntegerType>(CE->getType())->getBitWidth();
      GV.IntVal = GV.IntVal.trunc(BitWidth);
      return GV;
    }
    case Instruction::ZExt: {
      GenericValue GV = evaluate(Op0).getValue();
      uint32_t BitWidth = cast<IntegerType>(CE->getType())->getBitWidth();
      GV.IntVal = GV.IntVal.zext(BitWidth);
      return GV;
    }
    case Instruction::SExt: {
      GenericValue GV = evaluate(Op0).getValue();
      uint32_t BitWidth = cast<IntegerType>(CE->getType())->getBitWidth();
      GV.IntVal = GV.IntVal.sext(BitWidth);
      return GV;
    }
    case Instruction::FPTrunc: {
      // FIXME long double
      GenericValue GV = evaluate(Op0).getValue();
      GV.FloatVal = float(GV.DoubleVal);
      return GV;
    }
    case Instruction::FPExt: {
      // FIXME long double
      GenericValue GV = evaluate(Op0).getValue();
      GV.DoubleVal = double(GV.FloatVal);
      return GV;
    }
    case Instruction::UIToFP: {
      GenericValue GV = evaluate(Op0).getValue();
      if (CE->getType()->isFloatTy())
        GV.FloatVal = float(GV.IntVal.roundToDouble());
      else if (CE->getType()->isDoubleTy())
        GV.DoubleVal = GV.IntVal.roundToDouble();
      else if (CE->getType()->isX86_FP80Ty()) {
        APFloat apf = APFloat::getZero(APFloat::x87DoubleExtended());
        (void)apf.convertFromAPInt(GV.IntVal, false,
                                   APFloat::rmNearestTiesToEven);
        GV.IntVal = apf.bitcastToAPInt();
      }
      return GV;
    }
    case Instruction::SIToFP: {
      GenericValue GV = evaluate(Op0).getValue();
      if (CE->getType()->isFloatTy())
        GV.FloatVal = float(GV.IntVal.signedRoundToDouble());
      else if (CE->getType()->isDoubleTy())
        GV.DoubleVal = GV.IntVal.signedRoundToDouble();
      else if (CE->getType()->isX86_FP80Ty()) {
        APFloat apf = APFloat::getZero(APFloat::x87DoubleExtended());
        (void)apf.convertFromAPInt(GV.IntVal, true,
                                   APFloat::rmNearestTiesToEven);
        GV.IntVal = apf.bitcastToAPInt();
      }
      return GV;
    }
    case Instruction::FPToUI: // double->APInt conversion handles sign
    case Instruction::FPToSI: {
      GenericValue GV = evaluate(Op0).getValue();
      uint32_t BitWidth = cast<IntegerType>(CE->getType())->getBitWidth();
      if (Op0->getType()->isFloatTy())
        GV.IntVal = APIntOps::RoundFloatToAPInt(GV.FloatVal, BitWidth);
      else if (Op0->getType()->isDoubleTy())
        GV.IntVal = APIntOps::RoundDoubleToAPInt(GV.DoubleVal, BitWidth);
      else if (Op0->getType()->isX86_FP80Ty()) {
        APFloat apf = APFloat(APFloat::x87DoubleExtended(), GV.IntVal);
        uint64_t v;
        bool ignored;
        (void)apf.convertToInteger(makeMutableArrayRef(v), BitWidth,
                                   CE->getOpcode() == Instruction::FPToSI,
                                   APFloat::rmTowardZero, &ignored);
        GV.IntVal = v; // endian?
      }
      return GV;
    }
    case Instruction::PtrToInt: {
      auto OGV = evaluate(Op0);
      if (!OGV.hasValue())
        return llvm::None;
      GenericValue GV = OGV.getValue();

      uint32_t PtrWidth = getDataLayout().getTypeSizeInBits(Op0->getType());
      assert(PtrWidth <= 64 && "Bad pointer width");
      GV.IntVal = APInt(PtrWidth, uintptr_t(GV.PointerVal));
      uint32_t IntWidth = getDataLayout().getTypeSizeInBits(CE->getType());
      GV.IntVal = GV.IntVal.zextOrTrunc(IntWidth);
      return GV;
    }
    case Instruction::IntToPtr: {
      GenericValue GV = evaluate(Op0).getValue();
      uint32_t PtrWidth = getDataLayout().getTypeSizeInBits(CE->getType());
      GV.IntVal = GV.IntVal.zextOrTrunc(PtrWidth);
      assert(GV.IntVal.getBitWidth() <= 64 && "Bad pointer width");
      GV.PointerVal = PointerTy(uintptr_t(GV.IntVal.getZExtValue()));
      return GV;
    }
    case Instruction::BitCast: {
      GenericValue GV = evaluate(Op0).getValue();
      Type *DestTy = CE->getType();
      switch (Op0->getType()->getTypeID()) {
      default:
        llvm_unreachable("Invalid bitcast operand");
      case Type::IntegerTyID:
        assert(DestTy->isFloatingPointTy() && "invalid bitcast");
        if (DestTy->isFloatTy())
          GV.FloatVal = GV.IntVal.bitsToFloat();
        else if (DestTy->isDoubleTy())
          GV.DoubleVal = GV.IntVal.bitsToDouble();
        break;
      case Type::FloatTyID:
        assert(DestTy->isIntegerTy(32) && "Invalid bitcast");
        GV.IntVal = APInt::floatToBits(GV.FloatVal);
        break;
      case Type::DoubleTyID:
        assert(DestTy->isIntegerTy(64) && "Invalid bitcast");
        GV.IntVal = APInt::doubleToBits(GV.DoubleVal);
        break;
      case Type::PointerTyID:
        assert(DestTy->isPointerTy() && "Invalid bitcast");
        break; // evaluate(Op0)  above already converted it
      }
      return GV;
    }
    case Instruction::Add:
    case Instruction::FAdd:
    case Instruction::Sub:
    case Instruction::FSub:
    case Instruction::Mul:
    case Instruction::FMul:
    case Instruction::UDiv:
    case Instruction::SDiv:
    case Instruction::URem:
    case Instruction::SRem:
    case Instruction::And:
    case Instruction::Or:
    case Instruction::Xor: {
      GenericValue LHS = evaluate(Op0).getValue();
      GenericValue RHS = evaluate(CE->getOperand(1)).getValue();
      GenericValue GV;
      switch (CE->getOperand(0)->getType()->getTypeID()) {
      default:
        llvm_unreachable("Bad add type!");
      case Type::IntegerTyID:
        switch (CE->getOpcode()) {
        default:
          llvm_unreachable("Invalid integer opcode");
        case Instruction::Add:
          GV.IntVal = LHS.IntVal + RHS.IntVal;
          break;
        case Instruction::Sub:
          GV.IntVal = LHS.IntVal - RHS.IntVal;
          break;
        case Instruction::Mul:
          GV.IntVal = LHS.IntVal * RHS.IntVal;
          break;
        case Instruction::UDiv:
          GV.IntVal = LHS.IntVal.udiv(RHS.IntVal);
          break;
        case Instruction::SDiv:
          GV.IntVal = LHS.IntVal.sdiv(RHS.IntVal);
          break;
        case Instruction::URem:
          GV.IntVal = LHS.IntVal.urem(RHS.IntVal);
          break;
        case Instruction::SRem:
          GV.IntVal = LHS.IntVal.srem(RHS.IntVal);
          break;
        case Instruction::And:
          GV.IntVal = LHS.IntVal & RHS.IntVal;
          break;
        case Instruction::Or:
          GV.IntVal = LHS.IntVal | RHS.IntVal;
          break;
        case Instruction::Xor:
          GV.IntVal = LHS.IntVal ^ RHS.IntVal;
          break;
        }
        break;
      case Type::FloatTyID:
        switch (CE->getOpcode()) {
        default:
          llvm_unreachable("Invalid float opcode");
        case Instruction::FAdd:
          GV.FloatVal = LHS.FloatVal + RHS.FloatVal;
          break;
        case Instruction::FSub:
          GV.FloatVal = LHS.FloatVal - RHS.FloatVal;
          break;
        case Instruction::FMul:
          GV.FloatVal = LHS.FloatVal * RHS.FloatVal;
          break;
        case Instruction::FDiv:
          GV.FloatVal = LHS.FloatVal / RHS.FloatVal;
          break;
        case Instruction::FRem:
          GV.FloatVal = std::fmod(LHS.FloatVal, RHS.FloatVal);
          break;
        }
        break;
      case Type::DoubleTyID:
        switch (CE->getOpcode()) {
        default:
          llvm_unreachable("Invalid double opcode");
        case Instruction::FAdd:
          GV.DoubleVal = LHS.DoubleVal + RHS.DoubleVal;
          break;
        case Instruction::FSub:
          GV.DoubleVal = LHS.DoubleVal - RHS.DoubleVal;
          break;
        case Instruction::FMul:
          GV.DoubleVal = LHS.DoubleVal * RHS.DoubleVal;
          break;
        case Instruction::FDiv:
          GV.DoubleVal = LHS.DoubleVal / RHS.DoubleVal;
          break;
        case Instruction::FRem:
          GV.DoubleVal = std::fmod(LHS.DoubleVal, RHS.DoubleVal);
          break;
        }
        break;
      case Type::X86_FP80TyID:
      case Type::PPC_FP128TyID:
      case Type::FP128TyID: {
        const fltSemantics &Sem =
            CE->getOperand(0)->getType()->getFltSemantics();
        APFloat apfLHS = APFloat(Sem, LHS.IntVal);
        switch (CE->getOpcode()) {
        default:
          llvm_unreachable("Invalid long double opcode");
        case Instruction::FAdd:
          apfLHS.add(APFloat(Sem, RHS.IntVal), APFloat::rmNearestTiesToEven);
          GV.IntVal = apfLHS.bitcastToAPInt();
          break;
        case Instruction::FSub:
          apfLHS.subtract(APFloat(Sem, RHS.IntVal),
                          APFloat::rmNearestTiesToEven);
          GV.IntVal = apfLHS.bitcastToAPInt();
          break;
        case Instruction::FMul:
          apfLHS.multiply(APFloat(Sem, RHS.IntVal),
                          APFloat::rmNearestTiesToEven);
          GV.IntVal = apfLHS.bitcastToAPInt();
          break;
        case Instruction::FDiv:
          apfLHS.divide(APFloat(Sem, RHS.IntVal), APFloat::rmNearestTiesToEven);
          GV.IntVal = apfLHS.bitcastToAPInt();
          break;
        case Instruction::FRem:
          apfLHS.mod(APFloat(Sem, RHS.IntVal));
          GV.IntVal = apfLHS.bitcastToAPInt();
          break;
        }
      } break;
      }
      return GV;
    }
    default:
      break;
    }

    SmallString<256> Msg;
    raw_svector_ostream OS(Msg);
    OS << "ConstantExpr not handled: " << *CE;
    report_fatal_error(OS.str());
  }

  // Otherwise, we have a simple constant.
  GenericValue Result;
  switch (C->getType()->getTypeID()) {
  case Type::FloatTyID:
    Result.FloatVal = cast<ConstantFP>(C)->getValueAPF().convertToFloat();
    break;
  case Type::DoubleTyID:
    Result.DoubleVal = cast<ConstantFP>(C)->getValueAPF().convertToDouble();
    break;
  case Type::X86_FP80TyID:
  case Type::FP128TyID:
  case Type::PPC_FP128TyID:
    Result.IntVal = cast<ConstantFP>(C)->getValueAPF().bitcastToAPInt();
    break;
  case Type::IntegerTyID:
    Result.IntVal = cast<ConstantInt>(C)->getValue();
    break;
  case Type::PointerTyID:
    if (isa<ConstantPointerNull>(C))
      Result.PointerVal = nullptr;
    else if (const Function *F = dyn_cast<Function>(C)) {
      if (m_ctx) {
        Expr reg = m_ctx->getRegister(*F);
        if (reg) {
          Expr val = m_ctx->read(reg);
          if (m_ctx->alu().isNum(val)) {
            expr::mpz_class addr = m_ctx->alu().toNum(val);
            Result = PTOGV((void *)addr.get_ui());
            break;
          } else {
            LOG("opsem", WARN << "Function address " << *F
                              << " not numeric: " << *val << "\n";);
          }
        } else {
          LOG("opsem",
              WARN << "No register for function pointer: " << *F << "\n";);
        }
      }
      WARN << "Unhandled function pointer in a constant expression:  " << *C
           << "\n";
      return llvm::None;
    } else if (const GlobalVariable *GV = dyn_cast<GlobalVariable>(C)) {
      if (m_ctx) {
        Expr reg = m_ctx->getRegister(*GV);
        if (reg) {
          Expr val = m_ctx->read(reg);
          if (m_ctx->alu().isNum(val)) {
            expr::mpz_class num = m_ctx->alu().toNum(val);
            Result = PTOGV((void *)num.get_ui());
            LOG("opsem", errs() << "Evaluated addr of " << *GV << " to "
                                << llvm::format_hex(num.get_ui(), 16, true)
                                << "\n";);
            break;
          } else {
            LOG("opsem", WARN << "Value of global " << *GV
                              << " not numeric: " << *val << "\n";);
          }
        } else {
          LOG("opsem", WARN << "No register for global: " << *GV << "\n";);
        }
      }
      // TODO:
      // Result = PTOGV((void*)ctx.getPtrToGlobal(*GV));
      WARN << "Unhandled global variable in a constant expression: " << *C
           << "\n";
      return llvm::None;
    } else
      llvm_unreachable("Unknown constant pointer type!");
    break;
  case Type::VectorTyID: {
    unsigned elemNum;
    Type *ElemTy;
    const ConstantDataVector *CDV = dyn_cast<ConstantDataVector>(C);
    const ConstantVector *CV = dyn_cast<ConstantVector>(C);
    const ConstantAggregateZero *CAZ = dyn_cast<ConstantAggregateZero>(C);

    if (CDV) {
      elemNum = CDV->getNumElements();
      ElemTy = CDV->getElementType();
    } else if (CV || CAZ) {
      VectorType *VTy = dyn_cast<VectorType>(C->getType());
      elemNum = VTy->getNumElements();
      ElemTy = VTy->getElementType();
    } else {
      llvm_unreachable("Unknown constant vector type!");
    }

    Result.AggregateVal.resize(elemNum);
    // Check if vector holds floats.
    if (ElemTy->isFloatTy()) {
      if (CAZ) {
        GenericValue floatZero;
        floatZero.FloatVal = 0.f;
        std::fill(Result.AggregateVal.begin(), Result.AggregateVal.end(),
                  floatZero);
        break;
      }
      if (CV) {
        for (unsigned i = 0; i < elemNum; ++i)
          if (!isa<UndefValue>(CV->getOperand(i)))
            Result.AggregateVal[i].FloatVal =
                cast<ConstantFP>(CV->getOperand(i))
                    ->getValueAPF()
                    .convertToFloat();
        break;
      }
      if (CDV)
        for (unsigned i = 0; i < elemNum; ++i)
          Result.AggregateVal[i].FloatVal = CDV->getElementAsFloat(i);

      break;
    }
    // Check if vector holds doubles.
    if (ElemTy->isDoubleTy()) {
      if (CAZ) {
        GenericValue doubleZero;
        doubleZero.DoubleVal = 0.0;
        std::fill(Result.AggregateVal.begin(), Result.AggregateVal.end(),
                  doubleZero);
        break;
      }
      if (CV) {
        for (unsigned i = 0; i < elemNum; ++i)
          if (!isa<UndefValue>(CV->getOperand(i)))
            Result.AggregateVal[i].DoubleVal =
                cast<ConstantFP>(CV->getOperand(i))
                    ->getValueAPF()
                    .convertToDouble();
        break;
      }
      if (CDV)
        for (unsigned i = 0; i < elemNum; ++i)
          Result.AggregateVal[i].DoubleVal = CDV->getElementAsDouble(i);

      break;
    }
    // Check if vector holds integers.
    if (ElemTy->isIntegerTy()) {
      if (CAZ) {
        GenericValue intZero;
        intZero.IntVal = APInt(ElemTy->getScalarSizeInBits(), 0ull);
        std::fill(Result.AggregateVal.begin(), Result.AggregateVal.end(),
                  intZero);
        break;
      }
      if (CV) {
        for (unsigned i = 0; i < elemNum; ++i)
          if (!isa<UndefValue>(CV->getOperand(i)))
            Result.AggregateVal[i].IntVal =
                cast<ConstantInt>(CV->getOperand(i))->getValue();
          else {
            Result.AggregateVal[i].IntVal = APInt(
                CV->getOperand(i)->getType()->getPrimitiveSizeInBits(), 0);
          }
        break;
      }
      if (CDV)
        for (unsigned i = 0; i < elemNum; ++i)
          Result.AggregateVal[i].IntVal =
              APInt(CDV->getElementType()->getPrimitiveSizeInBits(),
                    CDV->getElementAsInteger(i));

      break;
    }
    llvm_unreachable("Unknown constant pointer type!");
  } break;
  case Type::StructTyID: {
    const auto *STy = dyn_cast<StructType>(C->getType());
    const auto *CS = dyn_cast<ConstantStruct>(C);
    const auto *CAZ = dyn_cast<ConstantAggregateZero>(C);
    if (!STy) {
      LOG("opsem", WARN << "unable to cast " << *C->getType() << " into a StructType";);
      return llvm::None;
    }
    unsigned int elemNum = STy->getNumElements();
    Result.AggregateVal.resize(elemNum);
    // try populate all elements in the struct
    for (unsigned int i = 0; i < elemNum; ++i) {
      Type *ElemTy = STy->getElementType(i);
      Constant *OPI;
      if (CS)
        OPI = CS->getOperand(i);
      else if (CAZ)
        OPI = UndefValue::get(ElemTy);
      else {
        LOG("opsem", WARN << "unsupported struct constant " << C;);
        return llvm::None;
      }
      if (isa<UndefValue>(OPI)) {
        // if field not defined, just return default garbage
        if (ElemTy->isIntegerTy()) {
          Result.AggregateVal[i].IntVal =
              APInt(ElemTy->getPrimitiveSizeInBits(), 0);
        } else if (ElemTy->isAggregateType()) {
          const Constant *ElemUndef = UndefValue::get(ElemTy);
          Result.AggregateVal[i] = evaluate(ElemUndef).getValue();
        } else if (ElemTy->isPointerTy()) {
          Result.AggregateVal[i].PointerVal = nullptr;
        }
      } else {
        if (ElemTy->isAggregateType() ||
            ElemTy->isIntegerTy() ||
            ElemTy->isPointerTy()) {
          auto val = evaluate(OPI);
          if (val.hasValue())
            Result.AggregateVal[i] = val.getValue();
          else {
            LOG("opsem",
                WARN << "evaluating struct, no value set on this index:" << i;);
            return llvm::None;
          }
        } else {
          LOG("opsem",
              WARN << "unsupported element type " << *ElemTy << " in const struct.";);
          return llvm::None;
        }
      }
    }
  } break;
  default:
    SmallString<256> Msg;
    raw_svector_ostream OS(Msg);
    OS << "ERROR: Constant unimplemented for type: " << *C->getType();
    report_fatal_error(OS.str());
  }

  return Result;
}

} // namespace details
} // namespace seahorn
