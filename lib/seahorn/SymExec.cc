#include "seahorn/SymExec.hh"

using namespace seahorn;

namespace 
{
  struct SymExecBase
  {
    SymStore &m_s;
    ExprFactory &m_efac;
    IntLightSymExec &m_sem;
    
    
    SymExecBase (SymStore &s, IntLightSymExec &sem) : 
      m_s(s), m_efac (s.getExprFactory ()), m_sem (sem) {}

    void read (const Value &v)
    {if (m_sem.isTracked (v)) m_s.read (symb (v));}
    
    Expr symb (const Value &I) {return m_sem.symb (I);}
    Expr lookup (const Value &v) {return m_sem.lookup (m_s, v);}
    Expr havoc (const Value &v) 
    {return m_sem.isTracked (v) ? m_s.havoc (symb (v)) : Expr (0);}
  };
  

  struct SymExecVisitor : public InstVisitor<SymExecVisitor> , 
                          SymExecBase
  {
    SymExecVisitor (SymStore &s, IntLightSymExec &sem) : SymExecBase (s, sem) {}
    
    void visitInstruction (Instruction &I) {havoc (I);}
    
    void visitPHINode (PHINode &I) {/* do nothing */}
    void visitReturnInst (ReturnInst &I) {lookup (*I.getOperand (0));}
    
    void visitBranchInst (BranchInst &I)
    {if (I.isConditional ()) lookup (*I.getOperand (0));}
    
    void visitBinaryOperator (BinaryOperator &I)
    {
      this->visitInstruction (I);
      lookup (*I.getOperand (0));
      lookup (*I.getOperand (1));
    }
    
    void visitCmpInst (CmpInst &I)
    {
      this->visitInstruction (I);
      lookup (*I.getOperand (0));
      lookup (*I.getOperand (1));
    }
    
    void visitCastInst (CastInst &I)
    {
      this->visitInstruction (I);
      lookup (*I.getOperand (0));
    }
  };

  struct SymExecPhiVisitor : public InstVisitor<SymExecPhiVisitor>,
                             SymExecBase
  {
    const BasicBlock &m_dst;
    
    SymExecPhiVisitor (SymStore &s, IntLightSymExec &sem, const BasicBlock &dst) : 
      SymExecBase (s, sem), m_dst (dst) {}
    
    void visitPHINode (PHINode &I) 
    {
      havoc (I);
      lookup (*I.getIncomingValueForBlock (&m_dst));
    }
  };

}

namespace seahorn
{
  void IntLightSymExec::exec (SymStore &s, const BasicBlock &bb, ExprVector &side)
  {
    SymExecVisitor v(s, *this);
    v.visit (const_cast<BasicBlock&>(bb));
  }
    
  void IntLightSymExec::exec (SymStore &s, const Instruction &inst, ExprVector &side)
  {
    SymExecVisitor v (s, *this);
    v.visit (const_cast<Instruction&>(inst));
  }
    
  
  void IntLightSymExec::execPhi (SymStore &s, const BasicBlock &bb, 
                                 const BasicBlock &from, ExprVector &side)
  {
    SymExecPhiVisitor v(s, *this, from);
    v.visit (const_cast<BasicBlock&>(bb));
  }

  void IntLightSymExec::execEdg (SymStore &s, const BasicBlock &src,
                                 const BasicBlock &dst, ExprVector &side)
  {
    exec (s, src, side);
    execPhi (s, dst, src, side);
  }
  
  void IntLightSymExec::execBr (SymStore &s, const BasicBlock &src, const BasicBlock &dst,
                                ExprVector &side)
  {
    if (const BranchInst* br = dyn_cast<const BranchInst> (src.getTerminator ()))
      if (br->isConditional ()) lookup (s, *br->getCondition ());
  }
  
  Expr IntLightSymExec::symb (const Value &I)
  {
    assert (I.getType ()->isIntegerTy ());
      
    Expr v = mkTerm<const Value*> (&I, m_efac);
    if (I.getType ()->isIntegerTy (1))
      v = bind::boolConst (v);
    else
      v = bind::intConst (v);
    return v;
  }
  
  const Value &IntLightSymExec::conc (Expr v)
  {
    assert (isOpX<FAPP> (v));
    // name of the app
    Expr u = bind::fname (v);
    // name of the fdecl
    u = bind::fname (u);
    assert (isOpX<VALUE> (v));
    return *getTerm<const Value*> (v);
  }
  
  
  bool IntLightSymExec::isTracked (const Value &v) {return v.getType ()->isIntegerTy ();}
  
  Expr IntLightSymExec::lookup (SymStore &s, const Value &v)
  {
    if (const ConstantInt *c = dyn_cast<const ConstantInt> (&v))
    {
      if (c->getType ()->isIntegerTy (1))
        return c->isOne () ? mk<TRUE> (m_efac) : mk<FALSE> (m_efac);
      mpz_class k = toMpz (c->getValue ());
      return mkTerm<mpz_class> (k, m_efac);
    }
    
    return isTracked (v) ? s.read (symb (v)) : Expr(0);
  }
  
 

}
