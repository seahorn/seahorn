#include "seahorn/CexExeGenerator.hh"

namespace seahorn {
namespace cexGen {
namespace utils {

template <typename kv>
bool extractArrayContents(Expr e, kv &out, Expr &defaultValue) {
  if (!e)
    return false;

  const MemMap a_map(e);
  if (!a_map.isValid()) {
    WARN << "cannot extract array contents " << *e;
    out.clear();
    return false;
  }
  Expr arrayDefault = a_map.getDefault();
  if (!arrayDefault) {
    WARN << "extract array contents, no default value" << *e;
    out.clear();
    return false;
  }
  defaultValue = arrayDefault;
  for (auto begin = a_map.cbegin(), end = a_map.cend(); begin != end; begin++) {
    Expr index = begin->getIdxExpr();
    Expr val = begin->getValueExpr();
    auto it = out.find(index);
    if (it != out.end()) {
      // we assume that indexes cannot be overwritten during
      // initialization
      WARN << "cannot extract array contents, duplicate found: " << *index;
      out.clear();
      return false;
    }
    out.insert(std::make_pair(index, val));
  }
  return true;
}
} // namespace utils

template <class Trace>
void CexExeGenerator<Trace>::storeMemHavoc(unsigned loc, const Function *func,
                                           ImmutableCallSite cs,
                                           ImmutableCallSite prevCS) {
  const Value *prevCV = prevCS.getCalledValue();
  const Function *prevF = dyn_cast<Function>(prevCV->stripPointerCasts());
  if (!(prevF && prevF->getName().equals("shadow.mem.load"))) {
    LOG("cex", errs() << "Skipping harness for memhavoc"
                      << " because shadow.mem.load cannot be found\n");
    return;
  }
  // get memhavoc content from corresponding shadow mem region
  auto *shadowMemI = dyn_cast<Instruction>(prevCS.getArgOperand(1));
  if (!shadowMemI)
    return;
  Expr shadowMem = m_trace.eval(loc, *shadowMemI, true);
  // get memhavoc size from second operand of memhavoc
  const Value *sizeArg = cs.getArgOperand(1);
  Expr size;
  if (auto *sizeI = dyn_cast<Instruction>(sizeArg)) {
    size = m_trace.eval(loc, *sizeI, true);
  } else if (auto *sizeConst = dyn_cast<ConstantInt>(sizeArg)) {
    expr::mpz_class sz = toMpz(sizeConst);
    size = expr::mkTerm<expr::mpz_class>(sz, m_trace.engine().efac());
  } else {
    LOG("cex",
        errs() << "unhandled Value of memhavoc size: " << *sizeArg << "\n");
    return;
  }
  // get info of ptr to havoc
  const Value *hPtrAlloc = cs.getArgOperand(0)->stripPointerCasts();
  Expr hPtrStart;
  if (auto *hPtrAllocInst = dyn_cast<Instruction>(hPtrAlloc)) {
    hPtrStart = m_trace.eval(loc, *hPtrAllocInst, true);
  } else {
    LOG("cex",
        errs() << "unhandled Value of memhavoc ptr: " << *hPtrAlloc << "\n");
    return;
  }
  Expr shadowMemRaw = m_trace.engine().getPtrAddressable(shadowMem);
  Expr hPtrStartRaw = m_trace.engine().getPtrAddressable(hPtrStart);
  if (!shadowMemRaw || !hPtrStartRaw || !size) {
    LOG("cex", errs() << "Skipping harness for memhavoc due to lacking info");
    return;
  }
  LOG("cex", errs() << "Producing harness for " << func->getName() << "\n";);
  m_func_val_map[func].push_back(shadowMemRaw);
  m_memhavoc_args.push_back(std::make_pair(hPtrStartRaw, size));
}

template <class Trace> void CexExeGenerator<Trace>::storeDataFromTrace() {
  for (unsigned loc = 0; loc < m_trace.size(); loc++) {
    const BasicBlock &BB = *m_trace.bb(loc);
    for (auto &I : BB) {
      if (const CallInst *ci = dyn_cast<CallInst>(&I)) {
        ImmutableCallSite CS(ci);
        // Go through bitcasts
        const Value *CV = CS.getCalledValue();
        const Function *CF = dyn_cast<Function>(CV->stripPointerCasts());
        if (!CF) {
          LOG("cex", errs() << "Skipping harness for " << *ci
                            << " because callee cannot be resolved\n");
          continue;
        }

        LOG("cex_verbose",
            errs() << "Considering harness for: " << CF->getName() << "\n";);

        if (CF->getName().equals("memhavoc")) {
          // previous instruction should be
          // shadow.mem.load(i32 x, i32 %sm_n, i8* null)
          if (I.getPrevNonDebugInstruction() == nullptr)
            continue;
          const Instruction *prevI = I.getPrevNonDebugInstruction();
          if (const CallInst *prevCi = dyn_cast<CallInst>(prevI)) {
            ImmutableCallSite prevCS(prevCi);
            storeMemHavoc(loc, CF, CS, prevCS);
          }
          continue;
        }

        if (!CF->hasName())
          continue;
        if (CF->isIntrinsic())
          continue;
        // We want to ignore seahorn functions, but not nondet
        // functions created by strip-extern or dummyMainFunction
        if (CF->getName().find_first_of('.') != StringRef::npos &&
            !CF->getName().startswith("verifier.nondet"))
          continue;
        if (!CF->isExternalLinkage(CF->getLinkage()))
          continue;
        if (!CF->getReturnType()->isIntegerTy() &&
            !CF->getReturnType()->isPointerTy()) {
          continue;
        }

        // KleeInternalize
        if (CF->getName().equals("calloc"))
          continue;

        // -- known library function
        LibFunc libfn;
        if (m_tli.getLibFunc(CF->getName(), libfn))
          continue;

        Expr V = m_trace.eval(loc, I, true);
        if (!V)
          continue;
        LOG("cex",
            errs() << "Producing harness for " << CF->getName() << "\n";);
        m_func_val_map[CF].push_back(V);
      }
    }
  }
}

template <class Trace>
void CexExeGenerator<Trace>::buildNonDetFunction(const Function *func,
                                                 ExprVector &values) {
  Function *func_impl = cast<Function>(
      m_harness
          ->getOrInsertFunction(func->getName(),
                                cast<FunctionType>(func->getFunctionType()))
          .getCallee());

  Type *RT = func->getReturnType();
  Type *pRT =
      RT->isIntegerTy() ? RT->getPointerTo() : Type::getInt8PtrTy(m_context);
  ArrayType *AT = ArrayType::get(RT, values.size());

  // Convert Expr to LLVM constants
  SmallVector<Constant *, 20> LLVMarray;
  std::transform(values.begin(), values.end(), std::back_inserter(LLVMarray),
                 [&RT, this](Expr e) { return exprToConstant(RT, e); });

  // This is an array containing the values to be returned
  GlobalVariable *CA =
      new GlobalVariable(*m_harness, AT, true, GlobalValue::PrivateLinkage,
                         ConstantArray::get(AT, LLVMarray));

  // Build the body of the harness function
  BasicBlock *BB = BasicBlock::Create(m_context, "entry", func_impl);
  IRBuilder<> Builder(BB);

  // invocation counter
  Type *CountType = Type::getInt32Ty(m_context);
  GlobalVariable *Counter = new GlobalVariable(*m_harness, CountType, false,
                                               GlobalValue::PrivateLinkage,
                                               ConstantInt::get(CountType, 0));
  Value *curCounter = Builder.CreateLoad(Counter);
  // increment counter
  Builder.CreateStore(
      Builder.CreateAdd(curCounter, ConstantInt::get(CountType, 1)), Counter);

  // build __seahorn_get_value_<type>(idx, CA, CA.size())
  std::string name;
  std::vector<Type *> ArgTypes = {CountType, pRT, CountType};
  std::vector<Value *> Args = {curCounter, Builder.CreateBitCast(CA, pRT),
                               ConstantInt::get(CountType, values.size())};

  if (RT->isIntegerTy()) {
    std::string RS;
    llvm::raw_string_ostream RSO(RS);
    RT->print(RSO);
    name = Twine("__seahorn_get_value_").concat(RSO.str()).str();
  } else if (RT->isPointerTy() ||
             RT->getTypeID() == llvm::ArrayType::ArrayTyID) {
    Type *elmTy = (RT->isPointerTy()) ? RT->getPointerElementType()
                                      : RT->getSequentialElementType();

    name = "__seahorn_get_value_ptr";
    ArgTypes.push_back(Type::getInt32Ty(m_context));

    // If we can tell how big the return type is, tell the
    // callback function.  Otherwise pass zero.
    if (elmTy->isSized())
      Args.push_back(ConstantInt::get(Type::getInt32Ty(m_context),
                                      m_dl.getTypeStoreSizeInBits(elmTy)));
    else
      Args.push_back(ConstantInt::get(Type::getInt32Ty(m_context), 0));
  } else {
    errs() << "WARNING: Unknown type: " << *RT << "\n";
    assert(false && "Unknown return type");
  }
  FunctionCallee GetValue = m_harness->getOrInsertFunction(
      name, FunctionType::get(RT, makeArrayRef(ArgTypes), false));
  assert(GetValue);
  Value *RetValue = Builder.CreateCall(GetValue, makeArrayRef(Args));
  Builder.CreateRet(RetValue);
}

template <class Trace>
void CexExeGenerator<Trace>::buildMemhavoc(const Function *func,
                                           ExprVector &values) {
  Function *func_impl = cast<Function>(
      m_harness
          ->getOrInsertFunction(func->getName(),
                                cast<FunctionType>(func->getFunctionType()))
          .getCallee());
  if (!func->getReturnType()->isVoidTy()) {
    LOG("cex", errs() << "memhavoc has non-void return type. Skipping...\n";);
    return;
  }
  Type *i8PtrTy = Type::getInt8PtrTy(m_context);
  // Convert Expr to LLVM constants
  SmallVector<Constant *, 20> LLVMarray;
  // one nested array for segments
  for (size_t i = 0; i < values.size(); i++) {
    auto havocPtr = m_memhavoc_args[i];
    Constant *segmentCA =
        exprToMemSegment(values[i], havocPtr.first, havocPtr.second);
    GlobalVariable *segmentGA =
        new GlobalVariable(*m_harness, segmentCA->getType(), true,
                           GlobalValue::PrivateLinkage, segmentCA);
    LLVMarray.push_back(ConstantExpr::getBitCast(segmentGA, i8PtrTy));
  }
  ArrayType *AT = ArrayType::get(i8PtrTy, LLVMarray.size());
  // This is an array containing the values to be returned
  GlobalVariable *CA =
      new GlobalVariable(*m_harness, AT, true, GlobalValue::PrivateLinkage,
                         ConstantArray::get(AT, LLVMarray));
  // Build the body of the harness function
  BasicBlock *BB = BasicBlock::Create(m_context, "entry", func_impl);
  IRBuilder<> Builder(BB);

  // invocation counter
  Type *CountType = Type::getInt32Ty(m_context);
  GlobalVariable *Counter = new GlobalVariable(*m_harness, CountType, false,
                                               GlobalValue::PrivateLinkage,
                                               ConstantInt::get(CountType, 0));
  Value *curCounter = Builder.CreateLoad(Counter);
  // increment counter
  Builder.CreateStore(
      Builder.CreateAdd(curCounter, ConstantInt::get(CountType, 1)), Counter);

  // build __seahorn_get_value_ptr(idx, CA, CA.size(), ebits = 0)
  // ebits = 0 since we are retrieving ptr to an array
  std::string name = "__seahorn_get_value_ptr";
  std::vector<Type *> ArgTypes = {CountType, i8PtrTy, CountType,
                                  Type::getInt32Ty(m_context)};
  std::vector<Value *> Args = {
      curCounter, Builder.CreateBitCast(CA, i8PtrTy),
      ConstantInt::get(CountType, values.size()),
      ConstantInt::get(Type::getInt32Ty(m_context), 0)};
  FunctionCallee GetValue = m_harness->getOrInsertFunction(
      name, FunctionType::get(i8PtrTy, makeArrayRef(ArgTypes), false));
  assert(GetValue);
  Value *RetValue = Builder.CreateCall(GetValue, makeArrayRef(Args));

  // void memcpy(i8* dst, i8* src, size_t block_len)
  FunctionCallee memCpy = m_harness->getOrInsertFunction(
      "memcpy", Type::getVoidTy(m_context), i8PtrTy, i8PtrTy,
      m_dl.getIntPtrType(m_context, 0));
  Builder.CreateCall(
      memCpy, {Builder.CreateBitCast(func_impl->getArg(0), i8PtrTy),
               Builder.CreateBitCast(RetValue, i8PtrTy), func_impl->getArg(1)});
  Builder.CreateRetVoid();
}

template <class Trace> void CexExeGenerator<Trace>::buildCexModule() {
  m_harness = std::make_unique<Module>("harness", m_context);
  m_harness->setDataLayout(m_dl);
  for (auto CFV : m_func_val_map) {

    auto CF = CFV.first;
    auto &values = CFV.second;
    if (CF->getName().equals("memhavoc")) {
      buildMemhavoc(CF, values);
    } else {
      buildNonDetFunction(CF, values);
    }
  }
}

template <class Trace>
void CexExeGenerator<Trace>::saveCexModuleToFile(llvm::StringRef CexFile) {
  std::error_code error_code;
  llvm::ToolOutputFile out(CexFile, error_code, sys::fs::F_None);
  assert(!error_code);
  verifyModule(*m_harness, &errs());
  if (CexFile.endswith(".ll"))
    out.os() << *m_harness;
  else
    WriteBitcodeToFile(*m_harness, out.os());
  out.os().close();
  out.keep();
}

template <class Trace>
Constant *CexExeGenerator<Trace>::exprToConstant(Type *ty, Expr e) {
  // sometimes ptr expression has struct encoding
  if (strct::isStructVal(e)) {
    Expr ePtr = m_trace.engine().getPtrAddressable(e);
    if (ePtr)
      return exprToConstant(ty, ePtr);
    else {
      LOG("cex", WARN << "Unhandled value: " << *e;);
      return Constant::getNullValue(ty);
    }
  }

  if (!ty->isIntegerTy() && !ty->isPointerTy()) {
    llvm_unreachable("[cex gen]: Unhandled type");
  }
  if (ty->isIntegerTy(1)) {
    // special handling for i1 types (true or false) because
    // getTypeStoreSizeInBits returns 8 for i1; instead use
    // getTrue and getFalse which always return i1
    if (isOpX<TRUE>(e)) {
      return ConstantInt::getTrue(m_context);
    } else if (isOpX<FALSE>(e)) {
      return ConstantInt::getFalse(m_context);
    } else {
      LOG("cex", WARN << "incompatible expression for i1 type: " << *e);
      return ConstantInt::getFalse(m_context);
    }
  }
  if (isOpX<TRUE>(e)) {
    return Constant::getIntegerValue(ty,
                                     APInt(m_dl.getTypeStoreSizeInBits(ty), 1));
  } else if (isOpX<FALSE>(e)) {
    return Constant::getIntegerValue(ty,
                                     APInt(m_dl.getTypeStoreSizeInBits(ty), 0));
  } else if (isOpX<MPZ>(e) || bv::is_bvnum(e)) {
    expr::mpz_class mpz;
    mpz = isOpX<MPZ>(e) ? getTerm<expr::mpz_class>(e)
                        : getTerm<expr::mpz_class>(e->arg(0));
    return Constant::getIntegerValue(
        ty, toAPInt(m_dl.getTypeStoreSizeInBits(ty), mpz));
  } else {
    LOG("cex",
        WARN << "value: " << *e << " is not compatible with type: " << *ty;);
    return Constant::getNullValue(ty);
  }
}

template <class Trace>
Constant *CexExeGenerator<Trace>::exprToMemSegment(Expr segment, Expr startAddr,
                                                   Expr size) {

  SmallVector<Constant *, 20> LLVMValueSegment;

  // total block size in bytes;
  expr::mpz_class sizeMpz;
  size_t blockWidth = 0;
  if (expr::numeric::getNum(size, sizeMpz)) {
    blockWidth = sizeMpz.get_ui();
  } else {
    LOG("cex",
        errs() << "memhavoc: cannot get concrete size (" << *size << ")\n");
    ArrayType *placeholderT = ArrayType::get(Type::getInt8PtrTy(m_context), 0);
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
    ArrayType *placeholderT = ArrayType::get(Type::getInt8PtrTy(m_context), 0);
    return ConstantArray::get(placeholderT, LLVMValueSegment);
  }

  const MemMap m_map(segment);
  if (!m_map.isValid()) {
    LOG("cex", errs() << "memhavoc: cannot extract content from: " << *segment
                      << "\n");
    ArrayType *placeholderT = ArrayType::get(Type::getInt8PtrTy(m_context), 0);
    return ConstantArray::get(placeholderT, LLVMValueSegment);
  }
  size_t elmWidth = m_map.getContentWidth();
  size_t blocks = std::ceil((float)blockWidth / (float)elmWidth);
  auto *segmentElmTy = IntegerType::get(m_context, elmWidth * 8);
  ArrayType *segmentAT = ArrayType::get(segmentElmTy, blocks);

  Expr defaultE = m_map.getDefault();
  // get default value or use 0 as fallback
  Constant *defaultConst;
  if (defaultE) {
    defaultConst = exprToConstant(segmentElmTy, defaultE);
  } else {
    LOG("cex", errs() << "havocing mem with default 0 \n");
    defaultConst = Constant::getIntegerValue(
        segmentElmTy, APInt(m_dl.getTypeStoreSizeInBits(segmentElmTy), 0));
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
      auto *segmentConst = exprToConstant(segmentElmTy, segmentE);
      LLVMValueSegment[index] = segmentConst;
    } else
      continue;
  }
  return ConstantArray::get(segmentAT, LLVMValueSegment);
}

template class CexExeGenerator<ZBmcTraceTy>;
template class CexExeGenerator<SolverBmcTraceTy>;

} // namespace cexGen
} // namespace seahorn
