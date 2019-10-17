#include "seahorn/MemSimulator.hh"
#include "seahorn/Support/SeaDebug.h"
#include "seahorn/Expr/ExprLlvm.hh"
#include "llvm/IR/InstVisitor.h"

#include "llvm/Analysis/MemoryBuiltins.h"
namespace seahorn {
using namespace llvm;
using namespace seahorn;
using namespace expr;

/*

  Addr : Int
  Oid : Int

  oid : Addr -> Oid
  start : Oid -> Int
  end : Oid -> Int
  sz(x) = end(x) - start(x)

  gep does not change oid
  load/store imply constraints on end of the corresponding oid
  allocation creates oid with a certain start and end
 */
struct MemSimVisitor : public InstVisitor<MemSimVisitor> {
  MemSimulator &m_sim;
  ExprVector &m_side;

  // -- map from concrete addresses to representative pointers
  ExprMap m_equiv;

  const BasicBlock *m_prev;
  unsigned m_loc;

  Expr m_largestPtr;
  Expr m_oidFn;
  Expr m_oidStartFn;
  Expr m_oidEndFn;

  MemSimVisitor(MemSimulator &sim, ExprVector &side)
      : m_sim(sim), m_side(side) {
    expr::mpz_class val;
    static const expr::mpz_class ones64(std::string("0xFFFFFFFFFFFFFFFF"));
    if (ptrSz() == 64)
      val = ones64;
    else if (ptrSz() == 32)
      val = 0xFFFFFFFF;
    else
      assert(false && "Unexpected pointer size");
    m_largestPtr = bv::bvnum(val, ptrSz(), efac());

    Expr bv = bv::bvsort(ptrSz(), efac());
    Expr sort[2] = {bv, bv};
    m_oidFn = bind::fdecl(mkTerm<std::string>("oid", efac()), sort);

    m_oidStartFn = bind::fdecl(mkTerm<std::string>("oid_start", efac()), sort);
    m_oidEndFn = bind::fdecl(mkTerm<std::string>("oid_end", efac()), sort);
  }

  ExprFactory &efac() { return m_sim.trace().engine().efac(); }

  void setPrev(const BasicBlock *bb) { m_prev = bb; }
  void setLoc(unsigned loc) { m_loc = loc; }

  unsigned ptrSz() const {
    return m_sim.getDataLayout().getPointerSizeInBits();
  }
  unsigned storeSz(const llvm::Type *t) const {
    return m_sim.getDataLayout().getTypeStoreSize(const_cast<Type *>(t));
  }
  unsigned storeSz(const llvm::Value *v) const { return storeSz(v->getType()); }

  void add(Expr c) { m_side.push_back(c); }
  void addEq(Expr lhs, Expr rhs) {
    if (lhs && rhs)
      add(mk<EQ>(lhs, rhs));
  }
  /// add value v to equivalence class c
  void addEquiv(Expr v, Expr c) {
    if (!v || !c)
      return;
    if (c == m_largestPtr)
      return;
    Expr &u = m_equiv[c];
    if (u)
      addEq(v, u);
    else
      u = v;
  }

  void addPtrDiff(Expr gep, Expr base, const expr::mpz_class &diff) {
    if (diff == expr::mpz_class())
      addEq(gep, base);
    else
      // AG: base + diff == gep might be simpler
      // add(mk<EQ>(mk<BADD>(base, ptrVal(diff)), gep);
      add(mk<EQ>(mk<BSUB>(gep, base), ptrVal(diff)));
  }

  Expr ptrVal(const expr::mpz_class &v) { return bv::bvnum(v, ptrSz(), efac()); }
  Expr symb(const Value &V) { return m_sim.trace().symb(m_loc, V); }
  Expr oidE(Expr e) { return bind::fapp(m_oidFn, e); }
  Expr startE(Expr e) { return bind::fapp(m_oidStartFn, oidE(e)); }
  Expr endE(Expr e) { return bind::fapp(m_oidEndFn, oidE(e)); }

  void visitCmpInst(CmpInst &I) {
    if (!I.getOperand(0)->getType()->isPointerTy())
      return;
    LOG("memsim", errs() << "  " << I << "\n";
        errs() << "\tval=" << *m_sim.trace().eval(m_loc, I) << "\n";);

    Expr op0 = symb(*I.getOperand(0));
    Expr op1 = symb(*I.getOperand(1));
    if (!op0 || !op1)
      return;

    Expr res;
    switch (I.getPredicate()) {
    case CmpInst::ICMP_EQ:
      res = mk<EQ>(op0, op1);
      break;
    case CmpInst::ICMP_NE:
      res = boolop::lneg(mk<EQ>(op0, op1));
      break;
    case CmpInst::ICMP_UGT:
      res = mk<BUGT>(op0, op1);
      break;
    case CmpInst::ICMP_ULT:
      res = mk<BULT>(op0, op1);
      break;
    default:
      assert(false && "NOT IMPLEMENTED");
    }

    if (res) {
      Expr val = m_sim.trace().eval(m_loc, I);
      if (isOpX<TRUE>(val))
        add(res);
      else if (isOpX<FALSE>(val))
        add(boolop::lneg(res));
    }
  }
  void visitPHINode(PHINode &I) {
    if (!I.getType()->isPointerTy())
      return;
    assert(m_prev);
    Value *phiVal = I.getIncomingValueForBlock(m_prev);
    addEq(symb(I), symb(*phiVal));
    visitInstruction(I);
  }
  void visitSelectInst(SelectInst &I) {
    if (!I.getType()->isPointerTy())
      return;
    Expr cVal = m_sim.trace().eval(m_loc, *I.getCondition());
    Value *val = nullptr;
    if (isOpX<TRUE>(cVal))
      val = I.getTrueValue();
    else if (isOpX<FALSE>(cVal))
      val = I.getFalseValue();

    if (val)
      addEq(symb(I), symb(*val));

    visitInstruction(I);
  }
  void visitPtrToIntInst(PtrToIntInst &I) {
    // I.getOperand (0) == eval(I)

    Expr val = m_sim.trace().eval(m_loc, I);
    Expr op = symb(*I.getOperand(0));
    if (val && op) {
      add(mk<EQ>(op, val));

      LOG("memsim", errs() << "  " << I << "\n";
          errs() << "\tval=" << *val << "\n";);
    }
  }
  void visitIntToPtrInst(IntToPtrInst &I) {
    Expr val = m_sim.trace().eval(m_loc, I);
    Expr op = symb(I);
    if (val && op) {
      add(mk<EQ>(op, val));

      LOG("memsim", errs() << "  " << I << "\n";
          errs() << "\tval=" << *val << "\n";);
    }
    visitInstruction(I);
  }
  void visitGetElementPtrInst(GetElementPtrInst &I) {
    // gep = gep.getPointerOperand () + (eval(gep) - eval(getPointerOperand ())

    Expr gepVal = m_sim.trace().eval(m_loc, I);
    Expr baseVal = m_sim.trace().eval(m_loc, *I.getPointerOperand());

    Expr gepPtr = symb(I);
    Expr basePtr = symb(*I.getPointerOperand());
    if (gepVal && baseVal && gepPtr && basePtr) {
      expr::mpz_class gepZ = bv::toMpz(gepVal);
      expr::mpz_class baseZ = bv::toMpz(baseVal);

      assert(baseZ <= gepZ);
      if (baseZ == gepZ)
        addEq(gepPtr, basePtr);
      else {
        assert(0 && "Dead broken code in comment below");
        addPtrDiff(gepPtr, basePtr, expr::mpz_class()/*gepZ - baseZ*/);
        add(mk<EQ>(oidE(gepPtr), oidE(basePtr)));
      }
    }

    visitInstruction(I);
  }

  void visitCallSite(CallSite CS) {
    // if instruction is an allocation, update size and pointer values
    if (llvm::isAllocationFn(CS.getInstruction(), &m_sim.getTargetLibraryInfo(),
                             true)) {

      LOG("memsim", errs() << "  ALLOCATION: ";);

      Instruction &I = *CS.getInstruction();
      uint64_t sz = 0;
      if (llvm::getObjectSize(&I, sz, m_sim.getDataLayout(),
                              &m_sim.getTargetLibraryInfo())) {
        LOG("memsim", errs() << sz;);
      } else {
        outs() << "\nWARNING: unsupported dynamically sized allocation\n";
        // -- TODO: extract symbolic definition of size and evaluate in the
        // model
        assert(false && "NOT IMPLEMENTED");
      }

      LOG("memsim", errs() << "\n";);

      auto &chunk = m_sim.alloc(sz);
      addEq(oidE(symb(I)), bv::bvnum(chunk.id, ptrSz(), efac()));
      addEq(startE(symb(I)), bv::bvnum(chunk.start, ptrSz(), efac()));
      addEq(endE(symb(I)), bv::bvnum(chunk.end, ptrSz(), efac()));
    }

    visitInstruction(*CS.getInstruction());
  }

  void visitAllocaInst(AllocaInst &I) {
    LOG("memsim", errs() << "  ALLOCATION: ";);

    uint64_t sz = 0;
    if (llvm::getObjectSize(&I, sz, m_sim.getDataLayout(),
                            &m_sim.getTargetLibraryInfo())) {
      LOG("memsim", errs() << sz;);
    } else {
      outs() << "\nWARNING: unsupported dynamically sized allocation\n";
      assert(false && "NOT IMPLEMENTED");
    }

    LOG("memsim", errs() << "\n";);

    auto &chunk = m_sim.alloc(sz);
    addEq(oidE(symb(I)), bv::bvnum(chunk.id, ptrSz(), efac()));
    addEq(startE(symb(I)), bv::bvnum(chunk.start, ptrSz(), efac()));
    addEq(endE(symb(I)), bv::bvnum(chunk.end, ptrSz(), efac()));

    // update size and pointer values
    visitInstruction(I);
  }
  void visitLoadInst(LoadInst &I) {
    LOG("memsim", errs() << "  " << I << "\n";);

    visitInstruction(I);

    Value *ptr = I.getPointerOperand();
    // start(oid(ptr)) <= ptr
    add(mk<BULE>(startE(symb(*ptr)), symb(*ptr)));
    // ptr + storeSz <= end (oid (ptr))

    Expr sz = bv::bvnum(storeSz(I.getType()), ptrSz(), efac());
    add(mk<BULE>(mk<BADD>(symb(*ptr), sz), endE(symb(*ptr))));
  }

  void visitStoreInst(StoreInst &I) {
    LOG("memsim", errs() << "  " << I << "\n";);
    Value *ptr = I.getPointerOperand();
    // start(oid(ptr)) <= ptr
    add(mk<BULE>(startE(symb(*ptr)), symb(*ptr)));

    // ptr + storeSz <= end (oid (ptr))
    Expr sz =
        bv::bvnum(storeSz(I.getValueOperand()->getType()), ptrSz(), efac());
    add(mk<BULE>(mk<BADD>(symb(*ptr), sz), endE(symb(*ptr))));
  }

  void visitCastInst(CastInst &I) {
    if (!I.getType()->isPointerTy())
      return;
    addEq(symb(I), symb(*I.getOperand(0)));

    // no call to visitInstruction(). All equivalence classes are
    // already attached to the operand
  }

  void visitInstruction(Instruction &I) {
    if (!I.getType()->isPointerTy())
      return;

    LOG("memsim", errs() << "  " << I << "\n";);

    Expr val = m_sim.trace().eval(m_loc, I);
    addEquiv(symb(I), val);
  }

  void visitGlobalVariable(const GlobalVariable &GV) {

    uint64_t sz;
    sz = storeSz(cast<PointerType>(GV.getType())->getElementType());

    LOG("memsim", errs() << "  ALLOCATION: " << sz << "\n";);
    // -- compute size of global based on size
    auto &chunk = m_sim.alloc(sz);
    addEq(oidE(symb(GV)), bv::bvnum(chunk.id, ptrSz(), efac()));
    addEq(startE(symb(GV)), bv::bvnum(chunk.start, ptrSz(), efac()));
    addEq(endE(symb(GV)), bv::bvnum(chunk.end, ptrSz(), efac()));

    LOG("memsim", errs() << GV << "\n";
        errs() << "\tval=" << *m_sim.trace().eval(m_loc, GV) << "\n";);
    addEquiv(symb(GV), m_sim.trace().eval(m_loc, GV));
  }
};

const MemSimulator::AllocInfo &MemSimulator::alloc(unsigned sz) {
  unsigned start = m_allocs.empty() ? m_intMemStart : m_allocs.back().end;
  AllocInfo *last = nullptr;

  m_allocs.push_back(AllocInfo());
  AllocInfo &n = m_allocs.back();

  n.id = m_allocs.size();
  n.start = start;
  n.end = n.start + sz;
  return n;
}

bool MemSimulator::simulate() {
  // extract module from trace
  if (m_trace.size() == 0)
    return false;
  const Module &M = *m_trace.bb(0)->getParent()->getParent();
  ExprVector side;
  MemSimVisitor v(*this, side);
  v.setPrev(nullptr);
  v.setLoc(0);
  for (auto it = M.global_begin(), end = M.global_end(); it != end; ++it)
    v.visitGlobalVariable(*it);

  const BasicBlock *last = nullptr;
  for (unsigned i = 0, sz = m_trace.size(); i < sz; ++i) {
    v.setPrev(last);
    v.setLoc(i);
    const BasicBlock *bb = m_trace.bb(i);
    v.visit(const_cast<BasicBlock *>(bb));
    last = bb;
  }

  ZSolver<EZ3> solver(zctx());
  LOG("memsim", errs() << "Constraints begin\n"; for (auto v
                                                      : side) {
    errs() << *v << "\n";
    solver.assertExpr(v);
  } errs() << "Constrains end\n";);

  for (auto v : side)
    solver.assertExpr(v);
  auto res = solver.solve();
  if (res) {
    LOG("memsim", errs() << "Memory simulation: Success\n";);
    m_model = solver.getModel();
    LOG("memsim", errs() << m_model << "\n";);
    return true;
  } else if (!res) {
    LOG("memsim", errs() << "Memory simulation: Failure\n";);
    // TODO: compute unsat core to explain the cause of failure
    return false;
  } else {
    LOG("memsim", errs() << "Memory simulation: Unknown!\n";);
    return false;
  }
}

Expr MemSimulator::eval(unsigned loc, const llvm::Instruction &inst,
                        bool complete) {
  if (!inst.getType()->isPointerTy())
    return m_trace.eval(loc, inst, complete);

  Expr v = m_trace.symb(loc, inst);
  if (v)
    v = m_model.eval(v, complete);
  return v;
}

Expr MemSimulator::eval(unsigned loc, Expr e, bool complete) {
  // return m_model.eval (e, complete);
  return m_trace.eval(loc, e, complete);
}

} // namespace seahorn
