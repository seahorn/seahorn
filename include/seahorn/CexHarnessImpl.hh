#include "seahorn/CexHarness.hh"

#include "llvm/Bitcode/BitcodeWriter.h"
#include "llvm/IR/DataLayout.h"
#include "llvm/IR/IRBuilder.h"
#include "llvm/IR/LLVMContext.h"
#include "llvm/IR/ValueMap.h"
#include "llvm/IR/Verifier.h"
#include "llvm/Support/FileSystem.h"
#include "llvm/Support/ToolOutputFile.h"

#include "seahorn/Transforms/Instrumentation/ShadowMemDsa.hh"

#include "boost/algorithm/string/replace.hpp"
#include "seahorn/Expr/ExprLlvm.hh"
#include "seahorn/Expr/ExprOpBinder.hh"
#include "seahorn/Support/SeaDebug.h"

namespace seahorn {

template <class Trace>
Expr BmcTraceWrapper<Trace>::eval(unsigned loc, const llvm::Instruction &inst,
                                  bool complete) {
  Expr v = m_trace.eval(loc, inst, complete);
  LOG("cex-eval", errs() << "Eval "
                         << "loc=" << loc << " " << inst << " --> " << v
                         << "\n");
  return v;
}

template <class Trace>
Expr BmcTraceWrapper<Trace>::eval(unsigned loc, Expr e, bool complete) {
  Expr v = m_trace.eval(loc, e, complete);
  LOG("cex-eval", errs() << "Eval "
                         << "loc=" << loc << " " << e << " --> " << v << "\n");
  return v;
}

// return true if success
template <typename IndexToValueMap>
bool extractArrayContents(Expr e, IndexToValueMap &out, Expr &default_value) {
  // HACK: first field of a struct representing memory is the actual memory
  if (strct::isStructVal(e)) {
    e = e->arg(0);
  }
  if (isOpX<CONST_ARRAY>(e)) {
    default_value = e->right();
    return true;
  }

  if (isOpX<STORE>(e)) {
    assert(e->arity() == 3);

    ExprVector kids(e->args_begin(), e->args_end());
    Expr array = kids[0];
    Expr index = kids[1];
    Expr val = kids[2];
    auto it = out.find(index);
    if (it != out.end()) {
      // we assume that indexes cannot be overwritten during
      // initialization
      WARN << "cannot extract array contents";
      out.clear();
      return false;
    }
    out.insert(std::make_pair(index, val));
    return extractArrayContents(array, out, default_value);
  } else if (isOpX<LAMBDA>(e)) {
    WARN << "arrays are lambdas (wip): " << *e;
    out.clear();
    return false;
  }
  WARN << "unsupported array term " << *e;
  out.clear();
  return false;
}

template <class Trace>
void dumpLLVMCex(BmcTraceWrapper<Trace> &trace, StringRef CexFile,
                 const DataLayout &dl, const TargetLibraryInfo &tli,
                 LLVMContext &context) {
  std::unique_ptr<Module> Harness = createCexHarness(trace, dl, tli, context);
  std::error_code error_code;
  llvm::ToolOutputFile out(CexFile, error_code, sys::fs::F_None);
  assert(!error_code);
  verifyModule(*Harness, &errs());
  if (CexFile.endswith(".ll"))
    out.os() << *Harness;
  else
    WriteBitcodeToFile(*Harness, out.os());
  out.os().close();
  out.keep();
}

template <class Trace>
std::unique_ptr<Module>
createCexHarness(BmcTraceWrapper<Trace> &trace, const DataLayout &dl,
                 const TargetLibraryInfo &tli, LLVMContext &TheContext) {
  std::unique_ptr<Module> Harness =
      std::make_unique<Module>("harness", TheContext);
  Harness->setDataLayout(dl);

  ValueMap<const Function *, ExprVector> FuncValueMap;
  // map a dsa node to start and end addresses
  std::map<unsigned, std::pair<Expr, Expr>> DsaAllocMap;
  // map a dsa node to its contents (as a pair of a default value
  // and a map from index to value)
  std::map<unsigned, std::pair<Expr, std::map<Expr, Expr>>> DsaContentMap;
  // store initialized mem size for memhavoc
  std::vector<std::pair<Expr, Expr>> HavocPtrs;

  // Look for calls in the trace
  for (unsigned loc = 0; loc < trace.size(); loc++) {
    const BasicBlock &BB = *trace.bb(loc);
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

        if (CF->getName().equals("shadow.mem.init")) {
          unsigned id = shadow_dsa::getShadowId(CS);
          ExprFactory &efac = trace.efac();
          Expr sort = bv::bvsort(dl.getPointerSizeInBits(), efac);
          Expr startE = shadow_dsa::memStartVar(id, sort);
          Expr endE = shadow_dsa::memEndVar(id, sort);
          Expr startV = trace.eval(loc, startE, true);
          Expr endV = trace.eval(loc, endE, true);
          DsaAllocMap.insert(std::make_pair(id, std::make_pair(startV, endV)));
          // 2) Get the contents of the lhs of shadow.mem.init
          //    list of (offset,value) plus default value ?
          Expr arrayE = trace.eval(loc, *ci, true);
          if (!arrayE) {
            DsaContentMap.erase(id);
            continue;
          }
          auto &p = DsaContentMap[id];
          bool res = extractArrayContents(arrayE, p.second, p.first);
          if (!res) {
            DsaContentMap.erase(id);
          }
          // we generate the harness even if we fail extracting the
          // array contents
          LOG("cex", errs()
                         << "Producing harness for " << CF->getName() << "\n";);
          continue;
        }
        if (CF->getName().equals("memhavoc")) {
          LOG("cex", errs()
                         << "Producing harness for " << CF->getName() << "\n";);
          // previous instruction should be
          // shadow.mem.load(i32 x, i32 %sm_n, i8* null)
          if (I.getPrevNonDebugInstruction() == nullptr)
            continue;
          const Instruction *prevI = I.getPrevNonDebugInstruction();
          if (const CallInst *prevCi = dyn_cast<CallInst>(prevI)) {
            ImmutableCallSite prevCS(prevCi);
            const Value *prevCV = prevCS.getCalledValue();
            const Function *prevCF =
                dyn_cast<Function>(prevCV->stripPointerCasts());
            if (!(prevCF && prevCF->getName().equals("shadow.mem.load"))) {
              LOG("cex", errs()
                             << "Skipping harness for " << CF->getName()
                             << " because shadow.mem.load cannot be found\n");
              continue;
            }
            // get memhavoc content from second operand of shadow.mem.load
            const Value *shadowMemPtr = prevCS.getArgOperand(1);
            const Instruction *shadowMemI = dyn_cast<Instruction>(shadowMemPtr);
            if (!shadowMemI)
              continue;
            Expr shadowMemV = trace.eval(loc, *shadowMemI, true);
            // get memhavoc size from second operand of memhavoc
            const Value *size = CS.getArgOperand(1);
            Expr sizeE;
            if (auto *sizeI = dyn_cast<Instruction>(size)) {
              sizeE = trace.eval(loc, *sizeI, true);
            } else if (auto *sizeConst = dyn_cast<ConstantInt>(size)) {
              expr::mpz_class sz = toMpz(sizeConst);
              sizeE = expr::mkTerm<expr::mpz_class>(sz, trace.efac());
            } else {
              LOG("cex", errs() << "unhandled Value of memhavoc size: " << *size
                                << "\n");
              continue;
            }
            // get info of ptr to havoc
            const Value *hPtr = CS.getArgOperand(0)->stripPointerCasts();
            Expr hPtrE;
            if (auto *hPtrAllocInst = dyn_cast<Instruction>(hPtr)) {
              hPtrE = trace.eval(loc, *hPtrAllocInst, true);
            } else {
              LOG("cex", errs() << "unhandled Value of memhavoc ptr: " << *hPtr
                                << "\n");
              continue;
            }

            FuncValueMap[CF].push_back(shadowMemV);
            HavocPtrs.push_back(std::make_pair(hPtrE->arg(0), sizeE));
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
          // LOG("cex",
          //     errs () << "Skipping harness for " << CF->getName ()
          //             << " because it returns type: " << *CF->getReturnType()
          //             << "\n";);
          continue;
        }

        // KleeInternalize
        if (CF->getName().equals("calloc"))
          continue;

        // -- known library function
        LibFunc libfn;
        if (tli.getLibFunc(CF->getName(), libfn))
          continue;

        Expr V = trace.eval(loc, I, true);
        if (!V)
          continue;
        LOG("cex",
            errs() << "Producing harness for " << CF->getName() << "\n";);
        FuncValueMap[CF].push_back(V);
      }
    }
  }

  // Build harness functions
  for (auto CFV : FuncValueMap) {

    auto CF = CFV.first;
    auto &values = CFV.second;

    // This is where we will build the harness function
    Function *HF = cast<Function>(
        Harness
            ->getOrInsertFunction(CF->getName(),
                                  cast<FunctionType>(CF->getFunctionType()))
            .getCallee());

    Type *RT = CF->getReturnType();
    Type *pRT = nullptr;
    if (RT->isIntegerTy())
      pRT = RT->getPointerTo();
    else
      pRT = Type::getInt8PtrTy(TheContext);

    ArrayType *AT = nullptr;

    // Convert Expr to LLVM constants
    SmallVector<Constant *, 20> LLVMarray;
    if (RT->isVoidTy()) {
      if (!CF->getName().equals("memhavoc")) {
        continue;
      }

      // one nested array for segments
      for (size_t i = 0; i < values.size(); i++) {
        auto havocPtr = HavocPtrs[i];
        Constant *segmentCA = exprToMemSegment(values[i], havocPtr.first,
                                               havocPtr.second, TheContext, dl);
        GlobalVariable *segmentGA =
            new GlobalVariable(*Harness, segmentCA->getType(), true,
                               GlobalValue::PrivateLinkage, segmentCA);
        LLVMarray.push_back(ConstantExpr::getBitCast(segmentGA, pRT));
      }
      AT = ArrayType::get(pRT, LLVMarray.size());
    } else {
      std::transform(values.begin(), values.end(),
                     std::back_inserter(LLVMarray),
                     [&RT, &dl, &TheContext](Expr e) {
                       return exprToLlvm(RT, e, TheContext, dl);
                     });
      AT = ArrayType::get(RT, values.size());
    }

    // This is an array containing the values to be returned
    GlobalVariable *CA =
        new GlobalVariable(*Harness, AT, true, GlobalValue::PrivateLinkage,
                           ConstantArray::get(AT, LLVMarray));

    // Build the body of the harness function
    BasicBlock *BB = BasicBlock::Create(TheContext, "entry", HF);
    IRBuilder<> Builder(BB);

    Type *CountType = Type::getInt32Ty(TheContext);
    GlobalVariable *Counter = new GlobalVariable(
        *Harness, CountType, false, GlobalValue::PrivateLinkage,
        ConstantInt::get(CountType, 0));

    Value *LoadCounter = Builder.CreateLoad(Counter);

    Builder.CreateStore(
        Builder.CreateAdd(LoadCounter, ConstantInt::get(CountType, 1)),
        Counter);

    std::string name;
    std::vector<Type *> ArgTypes = {CountType, pRT, CountType};
    std::vector<Value *> Args = {LoadCounter, Builder.CreateBitCast(CA, pRT),
                                 ConstantInt::get(CountType, values.size())};

    if (RT->isIntegerTy()) {
      std::string RS;
      llvm::raw_string_ostream RSO(RS);
      RT->print(RSO);

      name = Twine("__seahorn_get_value_").concat(RSO.str()).str();
    } else if (RT->isPointerTy() ||
               RT->getTypeID() == llvm::ArrayType::ArrayTyID ||
               RT->isVoidTy() /* memhavoc */) {
      Type *elmTy = nullptr;
      if (RT->isPointerTy())
        elmTy = RT->getPointerElementType();
      else if (RT->isVoidTy())
        elmTy =
            Type::getVoidTy(TheContext); // not interested in ebits for memhavoc
      else
        elmTy = RT->getSequentialElementType();

      name = "__seahorn_get_value_ptr";
      ArgTypes.push_back(Type::getInt32Ty(TheContext));

      // If we can tell how big the return type is, tell the
      // callback function.  Otherwise pass zero.
      if (elmTy->isSized())
        Args.push_back(ConstantInt::get(Type::getInt32Ty(TheContext),
                                        dl.getTypeStoreSizeInBits(elmTy)));
      else
        Args.push_back(ConstantInt::get(Type::getInt32Ty(TheContext), 0));
    } else {
      errs() << "WARNING: Unknown type: " << *RT << "\n";
      assert(false && "Unknown return type");
    }
    Type *GetType = RT->isVoidTy() ? pRT : RT;
    FunctionCallee GetValue = Harness->getOrInsertFunction(
        name, FunctionType::get(GetType, makeArrayRef(ArgTypes), false));
    assert(GetValue);
    Value *RetValue = Builder.CreateCall(GetValue, makeArrayRef(Args));

    if (RT->isVoidTy()) {
      // void memcpy(i8* dst, i8* src, size_t block_len)
      FunctionCallee memCpy = Harness->getOrInsertFunction(
          "memcpy", Type::getVoidTy(TheContext), pRT, pRT,
          dl.getIntPtrType(TheContext, 0));
      Builder.CreateCall(memCpy,
                         {Builder.CreateBitCast(HF->getArg(0), pRT),
                          Builder.CreateBitCast(RetValue, pRT), HF->getArg(1)});
      Builder.CreateRetVoid();
    } else
      Builder.CreateRet(RetValue);
  }

  {
    Type *intTy = IntegerType::get(TheContext, 64);
    Type *intPtrTy = dl.getIntPtrType(TheContext, 0);
    Type *i8PtrTy = Type::getInt8PtrTy(TheContext, 0);

    // Hook for gdb-like tools. Used to translate virtual addresses to
    // physical ones if that's the case. This is useful so we can
    // inspect content of virtual addresses.
    Function *EmvMapF = cast<Function>(
        Harness->getOrInsertFunction("__emv", i8PtrTy, i8PtrTy).getCallee());
    EmvMapF->addFnAttr(Attribute::NoInline);

    // Build function to initialize dsa nodes
    Function *InitF =
        cast<Function>(Harness
                           ->getOrInsertFunction("__seahorn_mem_init_routine",
                                                 Type::getVoidTy(TheContext))
                           .getCallee());
    // Build the body of the harness initialization function
    BasicBlock *BB = BasicBlock::Create(TheContext, "entry", InitF);
    IRBuilder<> Builder(BB);

    // Hook to allocate a dsa node
    Function *m_memAlloc =
        cast<Function>(Harness
                           ->getOrInsertFunction("__seahorn_mem_alloc",
                                                 Type::getVoidTy(TheContext),
                                                 i8PtrTy, i8PtrTy, intTy, intTy)
                           .getCallee());
    // Hook to initialize a dsa node
    Function *m_memInit =
        cast<Function>(Harness
                           ->getOrInsertFunction("__seahorn_mem_init",
                                                 Type::getVoidTy(TheContext),
                                                 i8PtrTy, intTy, intTy)
                           .getCallee());

    for (auto &kv : DsaAllocMap) {
      unsigned id = kv.first;
      std::pair<Expr, Expr> limits = kv.second;
      // LOG("cex",
      //     errs() << "Dsa node id=" << id << "\n"
      //            << "start=" << *(limits.first) << " "
      //            << "end=" << *(limits.second) << "\n";);

      std::map<Expr, Expr> contentVals;
      Expr defVal;

      // check if we have contents
      auto it = DsaContentMap.find(id);
      if (it != DsaContentMap.end()) {
        defVal = it->second.first;
        contentVals = it->second.second;
        // LOG("cex",
        //     errs () << "default value=" << *(defVal) << "\n";
        //     for (auto &kv: contentVals) {
        // 	errs () << *(kv.first) << "->" << *(kv.second) << "\n";
        //     });
      }

      // __seahorn_mem_alloc(start, end, val, sz);
      Value *startC = exprToLlvm(i8PtrTy, limits.first, TheContext, dl);
      Value *endC = exprToLlvm(i8PtrTy, limits.second, TheContext, dl);
      Value *valC = ConstantInt::get(intTy, 0);
      if (defVal) {
        valC = exprToLlvm(intTy, defVal, TheContext, dl);
      }

      Builder.CreateCall(
          m_memAlloc, {Builder.CreateBitCast(startC, i8PtrTy),
                       Builder.CreateBitCast(endC, i8PtrTy), valC,
                       ConstantInt::get(intTy, dl.getTypeStoreSize(intPtrTy))});

      // __seahorn_mem_init(index, val, sz)
      for (auto &kv : contentVals) {
        Value *indexC = exprToLlvm(i8PtrTy, kv.first, TheContext, dl);
        Value *valC = exprToLlvm(intTy, kv.second, TheContext, dl);
        Builder.CreateCall(
            m_memInit,
            {Builder.CreateBitCast(indexC, i8PtrTy), valC,
             ConstantInt::get(intTy, dl.getTypeStoreSize(intPtrTy))});
      }
    }
    Builder.CreateRetVoid();
  } // end AllocateMem

  return (Harness);
}
} // namespace seahorn
