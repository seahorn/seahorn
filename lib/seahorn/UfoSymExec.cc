/// Symbolic execution (loosely) based on semantics used in UFO
#include "llvm/IR/GetElementPtrTypeIterator.h"

#include "seahorn/UfoSymExec.hh"
#include "seahorn/Support/CFG.hh"

#include "ufo/ufo_iterators.hpp"
#include "llvm/Support/CommandLine.h"

#include <queue>

using namespace seahorn;
using namespace llvm;
using namespace ufo;

static llvm::cl::opt<bool>
GlobalConstraints("horn-global-constraints",
                  llvm::cl::desc
                  ("Maximize the use of global (i.e., unguarded) constraints"),
                  cl::init (false));

static llvm::cl::opt<bool>
StrictlyLinear ("horn-strictly-la",
                llvm::cl::desc ("Generate strictly Linear Arithmetic constraints"),
                cl::init (true));

static llvm::cl::opt<bool>
EnableDiv ("horn-enable-div",
                llvm::cl::desc ("Enable division constraints."),
                cl::init (true));


namespace
{
  struct SymExecBase
  {
    SymStore &m_s;
    ExprFactory &m_efac;
    UfoSmallSymExec &m_sem;
    ExprVector &m_side;
    
    Expr trueE;
    Expr falseE;
    
    /// -- current read memory
    Expr m_inMem;
    /// -- current write memory
    Expr m_outMem;
    
    /// -- parameters for a function call
    ExprVector m_fparams;
    
    Expr m_activeLit;
    
    SymExecBase (SymStore &s, UfoSmallSymExec &sem, ExprVector &side) : 
      m_s(s), m_efac (m_s.getExprFactory ()), m_sem (sem), m_side (side) 
    {
      trueE = mk<TRUE> (m_efac);
      falseE = mk<FALSE> (m_efac);
      resetActiveLit ();
      // -- first two arguments are reserved for error flag
      m_fparams.push_back (falseE);
      m_fparams.push_back (falseE);
      m_fparams.push_back (falseE);
    }
    Expr symb (const Value &I) {return m_sem.symb (I);}
    
    Expr read (const Value &v)
    {
      return m_sem.isTracked (v) ? m_s.read (symb (v)) : Expr (0);
    }

    Expr lookup (const Value &v) {return m_sem.lookup (m_s, v);}
    Expr havoc (const Value &v) 
    {return m_sem.isTracked (v) ? m_s.havoc (symb (v)) : Expr (0);}

    void resetActiveLit () {m_activeLit = trueE;}
    void setActiveLit (Expr act) {m_activeLit = act;}
    
    // -- add conditional side condition
    void addCondSide (Expr c) {m_side.push_back (boolop::limp (m_activeLit, c));}
    
  };
  
  struct SymExecVisitor : public InstVisitor<SymExecVisitor>, 
                          SymExecBase
  {
    SymExecVisitor (SymStore &s, UfoSmallSymExec &sem, ExprVector &side) : 
      SymExecBase (s, sem, side) {}
    
    /// base case. if all else fails.
    void visitInstruction (Instruction &I) {havoc (I);}
    
    /// skip PHI nodes
    void visitPHINode (PHINode &I) { /* do nothing */ }
    
     
    Expr geq (Expr op0, Expr op1)
    {
      if (op0 == op1) return trueE;
      if (isOpX<MPZ> (op0) && isOpX<MPZ> (op1))
        return
          getTerm<mpz_class> (op0) >=
          getTerm<mpz_class> (op1) ? trueE : falseE;
      
      return mk<GEQ> (op0, op1);
    }

    Expr lt (Expr op0, Expr op1)
    {
      if (op0 == op1) return falseE;
      if (isOpX<MPZ> (op0) && isOpX<MPZ> (op1))
        return
          getTerm<mpz_class> (op0) <
          getTerm<mpz_class> (op1) ? trueE : falseE;
      
      return mk<LT> (op0, op1);
    }
    
    Expr mkUnsignedLT (Expr op0, Expr op1)
    {
      Expr zero = mkTerm<mpz_class> (0, m_efac);
      using namespace expr::op::boolop;
      
      return lite (geq (op0, zero),
                      lite (geq (op1, zero),
                            lt (op0, op1),
                            trueE),
                      lite (lt (op1, zero),
                            lt (op0, op1),
                            falseE));
    }
    
    void visitCmpInst (CmpInst &I)
    {
      Expr lhs = havoc (I);
      
      const Value& v0 = *I.getOperand (0);
      const Value& v1 = *I.getOperand (1);
      
      Expr op0 = lookup (v0);
      Expr op1 = lookup (v1);

      if (!(op0 && op1)) return;

      Expr res;
      
      switch (I.getPredicate ())
      {
      case CmpInst::ICMP_EQ:
        res = mk<IFF>(lhs, mk<EQ>(op0,op1));
        break;
      case CmpInst::ICMP_NE:
        res = mk<IFF>(lhs, mk<NEQ>(op0,op1));
        break;
      case CmpInst::ICMP_UGT:
        res = mk<IFF> (lhs, mkUnsignedLT (op1, op0));
        break;
      case CmpInst::ICMP_SGT:
        res = mk<IFF>(lhs,mk<GT>(op0,op1));
        break;
      case CmpInst::ICMP_UGE:
        res = mk<OR> (mk<IFF> (lhs, mk<EQ> (op0, op1)),
                      mk<IFF> (lhs, mkUnsignedLT (op1, op0)));
        break;
      case CmpInst::ICMP_SGE:
        res = mk<IFF>(lhs,mk<GEQ>(op0,op1));
        break;
      case CmpInst::ICMP_ULT:
        res = mk<IFF> (lhs, mkUnsignedLT (op0, op1));
        break;
      case CmpInst::ICMP_SLT:
        res = mk<IFF>(lhs,mk<LT>(op0,op1));
        break; 
      case CmpInst::ICMP_ULE:
        res = mk<OR> (mk<IFF> (lhs, mk<EQ> (op0, op1)),
                      mk<IFF> (lhs, mkUnsignedLT (op0, op1)));
        break;
      case CmpInst::ICMP_SLE:
        res = mk<IFF>(lhs,mk<LEQ>(op0,op1));
        break;
      default:
        break;
      }       

      // -- optionally guard branch conditions by activation literals
      Expr act = GlobalConstraints ? trueE : m_activeLit;
      if (res)
        m_side.push_back (boolop::limp (act, res));
    }
    
    
    void visitSelectInst(SelectInst &I)
    {
      if (!m_sem.isTracked (I)) return;
      
      Expr lhs = havoc (I);
      Expr cond = lookup (*I.getCondition ());
      Expr op0 = lookup (*I.getTrueValue ());
      Expr op1 = lookup (*I.getFalseValue ());
      
      
      Expr act = GlobalConstraints ? trueE : m_activeLit;
      if (cond && op0 && op1)
        m_side.push_back (boolop::limp (act, mk<EQ> (lhs, mk<ITE> (cond, op0, op1))));
    }
    
    void visitBinaryOperator(BinaryOperator &I)
    {
      if (!m_sem.isTracked (I)) return;
      
      Expr lhs = havoc (I);
      
      switch (I.getOpcode ())
      {
      case BinaryOperator::Add:
      case BinaryOperator::Sub:
      case BinaryOperator::Mul:
      case BinaryOperator::UDiv:
      case BinaryOperator::SDiv:
      case BinaryOperator::Shl:
      case BinaryOperator::AShr:
      case BinaryOperator::SRem:
      case BinaryOperator::URem:
        doArithmetic (lhs, I);
        break;
          
      case BinaryOperator::And:
      case BinaryOperator::Or:
      case BinaryOperator::Xor:
      case BinaryOperator::LShr:
        doLogic(lhs, I);
        break;
      default:
        break;
      }
    }
    
    void doLogic (Expr lhs, BinaryOperator &i)
    {
      const Value& v0 = *(i.getOperand(0));
      const Value& v1 = *(i.getOperand(1));
      
      // only Boolean logic is supported
      if (! (v0.getType ()->isIntegerTy (1) &&
             v1.getType ()->isIntegerTy (1))) return;
      
      Expr op0 = lookup (v0);
      Expr op1 = lookup (v1);

      if (!(op0 && op1)) return;

      Expr res;
      
      switch(i.getOpcode())
	{
	case BinaryOperator::And:
	  res = mk<IFF>(lhs, mk<AND>(op0,op1));
          break;
	case BinaryOperator::Or:
	  res = mk<IFF>(lhs, mk<OR>(op0,op1));
          break;
        case BinaryOperator::Xor:
	  res = mk<IFF>(lhs, mk<XOR>(op0,op1));
          break;
        default:
          break;
	}

      Expr act = GlobalConstraints ? trueE : m_activeLit;
      if (res) m_side.push_back (boolop::limp (act, res));
    }

    Expr doLeftShift(Expr lhs, Expr op1, const ConstantInt *op2)
    {
      mpz_class shift = expr::toMpz (op2->getValue ());
      mpz_class factor = 1;
      for (unsigned long i = 0; i < shift.get_ui (); ++i) 
      {
          factor = factor * 2;
      }
      Expr res = mk<EQ>(lhs ,mk<MULT>(op1, mkTerm<mpz_class> (factor, m_efac)));        
      return res;
    }
    Expr doAShr (Expr lhs, Expr op1, const ConstantInt *op2)
    {
      if (!EnableDiv) return Expr(nullptr);
      
      mpz_class shift = expr::toMpz (op2->getValue ());
      mpz_class factor = 1;
      for (unsigned long i = 0; i < shift.get_ui (); ++i) 
          factor = factor * 2;
      return mk<EQ>(lhs ,mk<DIV>(op1, mkTerm<mpz_class> (factor, m_efac)));
    }
    


    void doArithmetic (Expr lhs, BinaryOperator &i)
    {
      const Value& v1 = *i.getOperand(0);
      const Value& v2 = *i.getOperand(1);

      Expr op1 = lookup (v1);
      Expr op2 = lookup (v2);

      if (!(op1 && op2)) return;

      Expr res;
      switch(i.getOpcode())
      {
      case BinaryOperator::Add:
        res = mk<EQ>(lhs ,mk<PLUS>(op1, op2));
        break;
      case BinaryOperator::Sub:
        res = mk<EQ>(lhs ,mk<MINUS>(op1, op2));
        break;
      case BinaryOperator::Mul:
        // if StrictlyLinear, then require that at least one
        // argument is a constant
        if (!StrictlyLinear || 
            isOpX<MPZ> (op1) || isOpX<MPZ> (op2) || 
            isOpX<MPQ> (op1) || isOpX<MPQ> (op2))
          res = mk<EQ>(lhs ,mk<MULT>(op1, op2));
        break;
      case BinaryOperator::SDiv:
      case BinaryOperator::UDiv:
        // if StrictlyLinear then require that divisor is a constant
        if (EnableDiv && 
            (!StrictlyLinear || 
             isOpX<MPZ> (op2) || isOpX<MPQ> (op2)))
          res = mk<EQ>(lhs ,mk<DIV>(op1, op2));
        break;
      case BinaryOperator::SRem:
      case BinaryOperator::URem:
        // if StrictlyLinear then require that divisor is a constant
        if (EnableDiv && 
            (!StrictlyLinear || isOpX<MPZ> (op2) || isOpX<MPQ> (op2)))
          res = mk<EQ> (lhs, mk<REM> (op1, op2));
        break;
      case BinaryOperator::Shl:
        if (const ConstantInt *ci = dyn_cast<ConstantInt> (&v2))
          res = doLeftShift(lhs, op1, ci);
        break;
      case BinaryOperator::AShr:
        if (const ConstantInt *ci = dyn_cast<ConstantInt> (&v2))
          res = doAShr (lhs, op1, ci);
        break;
      default:
        break;
      }

      Expr act = GlobalConstraints ? trueE : m_activeLit;
      if (res) m_side.push_back (boolop::limp (act, res));
    }
    
    void visitReturnInst (ReturnInst &I)
    {
      // -- skip return argument of main
      if (I.getParent ()->getParent ()->getName ().equals ("main")) return;
      
      if (I.getNumOperands () > 0)
        lookup (*I.getOperand (0));
    }
    
    void visitBranchInst (BranchInst &I)
    {
      if (I.isConditional ()) lookup (*I.getCondition ());
    }

    void visitTruncInst(TruncInst &I)              
    {
      if (!m_sem.isTracked (I)) return;
      Expr lhs = havoc (I);
      Expr op0 = lookup (*I.getOperand (0));
      
      if (!op0) return;

      Expr act = GlobalConstraints ? trueE : m_activeLit;
      if (I.getType ()->isIntegerTy (1))
      {
        Expr zero = mkTerm<mpz_class> (0, m_efac);
        Expr one = mkTerm<mpz_class> (1, m_efac);
      
        // truncation to 1 bit amounts to 'is_even' predicate.
        // We handle the two most common cases: 0 -> false, 1 -> true
        m_side.push_back (boolop::limp (act,
                                        mk<IMPL> (mk<EQ> (op0, zero), mk<NEG> (lhs))));
        m_side.push_back (boolop::limp (act,
                                        mk<IMPL> (mk<EQ> (op0, one), lhs)));
      }
      else
        m_side.push_back (boolop::limp (act, mk<EQ> (lhs, op0)));
    }
    
    void visitZExtInst (ZExtInst &I) {doExtCast (I, false);}
    void visitSExtInst (SExtInst &I) {doExtCast (I, true);}
    
    void visitGetElementPtrInst (GetElementPtrInst &gep)
    {
      if (!m_sem.isTracked (gep)) return;
      Expr lhs = havoc (gep);
      
      SmallVector<const Value*, 4> ps;
      SmallVector<const Type*, 4> ts;
      gep_type_iterator typeIt = gep_type_begin (gep);
      for (unsigned i = 1; i < gep.getNumOperands (); ++i, ++typeIt)
      {
        ps.push_back (gep.getOperand (i));
        ts.push_back (*typeIt);
      }
      
      Expr op = m_sem.ptrArith (m_s, *gep.getPointerOperand (), ps, ts);
      Expr act = GlobalConstraints ? trueE : m_activeLit;
      if (op) m_side.push_back (boolop::limp (act, mk<EQ> (lhs, op)));
    }
    
    void doExtCast (CastInst &I, bool is_signed = false)
    {
      Expr lhs = havoc (I);
      const Value& v0 = *I.getOperand (0);
      Expr op0 = lookup (v0);
      
      if (!op0) return;
      
      // sext maps (i1 1) to -1
      Expr one = mkTerm<mpz_class> (is_signed ? -1 : 1, m_efac);
      Expr zero = mkTerm<mpz_class> (0, m_efac);
      
      if (v0.getType ()->isIntegerTy (1))
      {
        if (const ConstantInt *ci = dyn_cast<ConstantInt> (&v0))
          op0 = ci->isOne () ? one : zero;
        else
          op0 = mk<ITE> (op0, one, zero);
      }
      
      Expr act = GlobalConstraints ? trueE : m_activeLit;
      m_side.push_back (boolop::limp (act, mk<EQ> (lhs, op0)));
    }
    
    void visitCallSite (CallSite CS)
    {
      assert (CS.isCall ());
      const Function *f = CS.getCalledFunction ();
      
      Instruction &I = *CS.getInstruction ();
      BasicBlock &BB = *I.getParent ();
      
      // -- unknown/indirect function call
      if (!f)
      { 
        // XXX Use DSA and/or Devirt to handle better
        assert (m_fparams.size () == 3);
        visitInstruction (I);
        return;
      }
      
      const Function &F = *f;
      const Function &PF = *I.getParent ()->getParent ();
      
      // skip intrinsic functions
      if (F.isIntrinsic ()) { assert (m_fparams.size () == 3); return;}
    
      
      if (F.getName ().startswith ("verifier.assume"))
      {
        Expr c = lookup (*CS.getArgument (0));
        if (F.getName ().equals ("verifier.assume.not")) c = boolop::lneg (c);
        
        assert (m_fparams.size () == 3);
        // -- assumption is only active when error flag is false
        addCondSide (boolop::lor (m_s.read (m_sem.errorFlag (BB)), c));
      }
      // else if (F.getName ().equals ("verifier.assert"))
      // {
      //   Expr ein = m_s.read (m_sem.errorFlag ());
      //   Expr eout = m_s.havoc (m_sem.errorFlag ());
      //   Expr cond = lookup (*CS.getArgument (0));
      //   m_side.push_back (boolop::limp (cond,
      //                                   mk<EQ> (ein, eout)));
      //   m_side.push_back (boolop::limp (boolop::lneg (cond), eout));
      // }
      // else if (F.getName ().equals ("verifier.error"))
      //   m_side.push_back (m_s.havoc (m_sem.errorFlag ()));
      else if (m_sem.hasFunctionInfo (F))
      {
        const FunctionInfo &fi = m_sem.getFunctionInfo (F);
        
        // enabled
        m_fparams [0] = m_activeLit; // activation literal
        // error flag in
        m_fparams [1] = (m_s.read (m_sem.errorFlag (BB)));
        // error flag out
        m_fparams [2] = (m_s.havoc (m_sem.errorFlag (BB)));
        for (const Argument *arg : fi.args)
          m_fparams.push_back (m_s.read (symb (*CS.getArgument (arg->getArgNo ()))));
        for (const GlobalVariable *gv : fi.globals)
          m_fparams.push_back (m_s.read (symb (*gv)));
        
        if (fi.ret) m_fparams.push_back (m_s.havoc (symb (I)));
        
        LOG ("arg_error", 
             if (m_fparams.size () != bind::domainSz (fi.sumPred))
             {
               errs () << "Call instruction: " << I << "\n";
               errs () << "Caller: " << PF << "\n";
               errs () << "Callee: " << F << "\n";
               // errs () << "Sum predicate: " << *fi.sumPred << "\n";
               errs () << "m_fparams.size: " << m_fparams.size () << "\n";
               errs () << "Domain size: " << bind::domainSz (fi.sumPred) << "\n";
               errs () << "m_fparams\n";
               for (auto r : m_fparams) errs () << *r << "\n";
               errs () << "regions: " << fi.regions.size () 
                       << " args: " << fi.args.size () 
                       << " globals: " << fi.globals.size () 
                       << " ret: " << fi.ret << "\n";
               errs () << "regions\n";
               for (auto r : fi.regions) errs () << *r << "\n";
               errs () << "args\n";
               for (auto r : fi.args) errs () << *r << "\n";
               errs () << "globals\n";
               for (auto r : fi.globals) errs () << *r << "\n";
               if (fi.ret) errs () << "ret: " << *fi.ret << "\n";
             }
             );
        
        assert (m_fparams.size () == bind::domainSz (fi.sumPred));
        m_side.push_back (bind::fapp (fi.sumPred, m_fparams));
        
        m_fparams.clear ();
        m_fparams.push_back (falseE);
        m_fparams.push_back (falseE);
        m_fparams.push_back (falseE);
      }
      else if (F.getName ().startswith ("shadow.mem") && 
               m_sem.isTracked (I))
      {
        if (F.getName ().equals ("shadow.mem.init"))
          m_s.havoc (symb(I));
        else if (F.getName ().equals ("shadow.mem.load"))
        {
          const Value &v = *CS.getArgument (1);
          m_inMem = m_s.read (symb (v));
        }
        else if (F.getName ().equals ("shadow.mem.store"))
        {
          m_inMem = m_s.read (symb (*CS.getArgument (1)));
          m_outMem = m_s.havoc (symb (I));
        }
        else if (F.getName ().equals ("shadow.mem.arg.ref"))
          m_fparams.push_back (m_s.read (symb (*CS.getArgument (1))));
        else if (F.getName ().equals ("shadow.mem.arg.mod"))
        {
          m_fparams.push_back (m_s.read (symb (*CS.getArgument (1))));
          m_fparams.push_back (m_s.havoc (symb (I)));
        }
        else if (F.getName ().equals ("shadow.mem.arg.new"))
          m_fparams.push_back (m_s.havoc (symb (I)));
        else if (!PF.getName ().equals ("main") && 
                 F.getName ().equals ("shadow.mem.in"))
        {
          m_s.read (symb (*CS.getArgument (1)));
        }
        else if (!PF.getName ().equals ("main") &&
                 F.getName ().equals ("shadow.mem.out"))
        {
          m_s.read (symb (*CS.getArgument (1)));
        }
        else if (!PF.getName ().equals ("main") && 
                 F.getName ().equals ("shadow.mem.arg.init"))
        {
          // regions initialized in main are global. We want them to
          // flow to the arguments
          /* do nothing */
        }
      }
      else
      {
        if (m_fparams.size () > 3)
        {
          m_fparams.resize (3);
          errs () << "WARNING: skipping a call to " << F.getName () 
                  << " (recursive call?)\n";
        }
        
        visitInstruction (*CS.getInstruction ());
      }
          
    }
    
    void visitLoadInst (LoadInst &I)
    {
      if (!m_sem.isTracked (I)) return;
      // -- define (i.e., use) the value of the instruction
      Expr lhs = havoc (I);
      if (!m_inMem) return;
      
      Expr op0 = lookup (*I.getPointerOperand ());
      
      if (op0)
      {
        Expr rhs = op::array::select (m_inMem, op0);
        if (I.getType ()->isIntegerTy (1))
          // -- convert to Boolean
          rhs = mk<NEQ> (rhs, mkTerm (mpz_class(0), m_efac));

        Expr act = GlobalConstraints ? trueE : m_activeLit;
        m_side.push_back (boolop::limp (act,
                                        mk<EQ> (lhs, rhs)));
      }
      
      m_inMem.reset ();
    }
    
    void visitStoreInst (StoreInst &I)
    {
      if (!m_inMem || !m_outMem || !m_sem.isTracked (*I.getOperand (0))) return;
      
      Expr idx = lookup (*I.getPointerOperand ());
      Expr v = lookup (*I.getOperand (0));
      
      if (v && I.getOperand (0)->getType ()->isIntegerTy (1))
        // -- convert to int
        v = boolop::lite (v, mkTerm (mpz_class (1), m_efac),
                          mkTerm (mpz_class (0), m_efac));
      
      Expr act = GlobalConstraints ? trueE : m_activeLit;
      if (idx && v)
        m_side.push_back (boolop::limp (act,
                                        mk<EQ> (m_outMem, 
                                                op::array::store (m_inMem, idx, v))));
      m_inMem.reset ();
      m_outMem.reset ();
    }
    
    
    void visitCastInst (CastInst &I)
    {
      if (!m_sem.isTracked (I)) return;

      Expr lhs = havoc (I);
      const Value &v0 = *I.getOperand (0);
      
      Expr act = GlobalConstraints ? trueE : m_activeLit;
      Expr u = lookup (v0);
      if (u) m_side.push_back (boolop::limp (act, mk<EQ> (lhs, u)));
    }
    
    void initGlobals (const BasicBlock &BB)
    {
      const Function &F = *BB.getParent ();
      if (&F.getEntryBlock () != &BB) return;
      if (!F.getName ().equals ("main")) return;
      
      const Module &M = *F.getParent ();
      for (const GlobalVariable &g : boost::make_iterator_range (M.global_begin (),
                                                                 M.global_end ()))
        if (m_sem.isTracked (g)) havoc (g);
    }
    
    void visitBasicBlock (BasicBlock &BB)
    {
      /// -- check if globals need to be initialized
      initGlobals (BB);
      
      // read the error flag to make it live
      m_s.read (m_sem.errorFlag (BB));
    }
    
  };
    
  struct SymExecPhiVisitor : public InstVisitor<SymExecPhiVisitor>,
                             SymExecBase
  {
    const BasicBlock &m_dst;
    
    SymExecPhiVisitor (SymStore &s, UfoSmallSymExec &sem, 
                       ExprVector &side, const BasicBlock &dst) : 
      SymExecBase (s, sem, side), m_dst (dst) {}
    
    void visitPHINode (PHINode &I) 
    {
      if (!m_sem.isTracked (I)) return;
      
      const Value &v = *I.getIncomingValueForBlock (&m_dst);

      Expr op0 = lookup (v);
      // -- phi node can read and write the same register. Thus, we
      // -- must first lookup the value of the argument, and only then
      // -- havoc the register.
      Expr lhs = havoc (I);
      Expr act = GlobalConstraints ? trueE : m_activeLit;
      if (op0) m_side.push_back (boolop::limp (act, mk<EQ> (lhs, op0)));
    }

  };
}

namespace seahorn
{
  Expr UfoSmallSymExec::errorFlag (const BasicBlock &BB)
  {
    // -- if BB belongs to a function that cannot fail, errorFlag is always false
    if (m_canFail && !m_canFail->canFail (BB.getParent ())) return falseE;
    return this->SmallStepSymExec::errorFlag (BB);
  }
  
  void UfoSmallSymExec::exec (SymStore &s, const BasicBlock &bb, ExprVector &side,
                              Expr act)
  {
    SymExecVisitor v(s, *this, side);
    v.setActiveLit (act);
    v.visit (const_cast<BasicBlock&>(bb));
    v.resetActiveLit ();
  }
    
  void UfoSmallSymExec::exec (SymStore &s, const Instruction &inst, ExprVector &side)
  {
    SymExecVisitor v (s, *this, side);
    v.visit (const_cast<Instruction&>(inst));
  }
    
  
  void UfoSmallSymExec::execPhi (SymStore &s, const BasicBlock &bb, 
                                 const BasicBlock &from, ExprVector &side, Expr act)
  {
    // act is ignored since phi node only introduces a definition
    SymExecPhiVisitor v(s, *this, side, from);
    v.setActiveLit (act);
    v.visit (const_cast<BasicBlock&>(bb));
    v.resetActiveLit ();
  }

  Expr UfoSmallSymExec::ptrArith (SymStore &s, 
                                  const Value &base,
                                  SmallVectorImpl<const Value*> &ps,
                                  SmallVectorImpl<const Type*> &ts)
  {
    Expr res = lookup (s, base);
    if (!res) return res;
    
    for (unsigned i = 0; i < ps.size (); ++i)
    {
      if (const StructType *st = dyn_cast<const StructType> (ts [i]))
      {
        if (const ConstantInt *ci = dyn_cast<const ConstantInt> (ps [i]))
        {
          Expr off = mkTerm<mpz_class> (fieldOff (st, ci->getZExtValue ()), m_efac);
          res = mk<PLUS> (res, off);
        }
        else assert (0);
      }
      else if (const SequentialType *seqt = dyn_cast<const SequentialType> (ts [i]))
      {
        Expr sz = mkTerm<mpz_class> (storageSize (seqt->getElementType ()), m_efac);
        res = mk<PLUS> (res, mk<MULT> (lookup (s, *ps[i]), sz));
      }
    }
    return res;
  }
  
  unsigned UfoSmallSymExec::storageSize (const llvm::Type *t) 
  {return m_td->getTypeStoreSize (const_cast<Type*> (t));}
  
  unsigned UfoSmallSymExec::fieldOff (const StructType *t, unsigned field)
  {
    return m_td->getStructLayout (const_cast<StructType*>(t))->getElementOffset (field);
  }
  
  bool UfoSmallSymExec::isShadowMem (const Value &V)
  {
    // work list
    std::queue<const Value*> wl;
    
    wl.push (&V);
    while (!wl.empty ())
    {
      const Value *val = wl.front ();
      wl.pop ();
      
      if (const CallInst *ci = dyn_cast<const CallInst> (val))
      {
        if (const Function *fn = ci->getCalledFunction ())
          return fn->getName ().startswith ("shadow.mem.");
        return false;
      }   
      else if (const PHINode *phi = dyn_cast<const PHINode> (val))
      {
        for (unsigned i = 0; i < phi->getNumIncomingValues (); ++i)
          wl.push (phi->getIncomingValue (i));
      }
      else return false;
    }
    
    assert (0);
    return false;
  }
  
  Expr UfoSmallSymExec::symb (const Value &I)
  {
    assert (!isa<UndefValue>(&I));

    // -- basic blocks are mapped to Bool constants
    if (const BasicBlock *bb = dyn_cast<const BasicBlock> (&I))
      return bind::boolConst 
        (mkTerm<const BasicBlock*> (bb, m_efac));
    
    // -- constants are mapped to values
    if (const Constant *cv = dyn_cast<const Constant> (&I))
    {
      if (const ConstantInt *c = dyn_cast<const ConstantInt> (&I))
      {
        if (c->getType ()->isIntegerTy (1))
          return c->isOne () ? mk<TRUE> (m_efac) : mk<FALSE> (m_efac);
        mpz_class k = toMpz (c->getValue ());
        return mkTerm<mpz_class> (k, m_efac);
      }
      else if (cv->isNullValue () || isa<ConstantPointerNull> (&I))
        return mkTerm<mpz_class> (0, m_efac);
      else if (const ConstantExpr *ce = dyn_cast<const ConstantExpr> (&I))
      {
        // -- if this is a cast, and not into a Boolean, strip it
        // -- XXX handle Boolean casts if needed
        if (ce->isCast () && 
            (ce->getType ()->isIntegerTy () || ce->getType ()->isPointerTy ()) && 
            ! ce->getType ()->isIntegerTy (1))
   
        {
          if (const ConstantInt* val = dyn_cast<const ConstantInt>(ce->getOperand (0)))
          {
            mpz_class k = toMpz (val->getValue ());
            return mkTerm<mpz_class> (k, m_efac);
          }
          // -- strip cast
          else return symb (*ce->getOperand (0));
        }
      }
    }   
     
    // -- everything else is mapped to a constant
    Expr v = mkTerm<const Value*> (&I, m_efac);
    
    if (m_trackLvl >= MEM && isShadowMem (I))
    {
      Expr intTy = sort::intTy (m_efac);
      Expr ty = sort::arrayTy (intTy, intTy);
      return bind::mkConst (v, ty);
    }
      
    if (isTracked (I))
      return I.getType ()->isIntegerTy (1) ? 
        bind::boolConst (v) : bind::intConst (v);
    
    return Expr(0);
  }
  
  const Value &UfoSmallSymExec::conc (Expr v)
  {
    assert (isOpX<FAPP> (v));
    // name of the app
    Expr u = bind::fname (v);
    // name of the fdecl
    u = bind::fname (u);
    assert (isOpX<VALUE> (v));
    return *getTerm<const Value*> (v);
  }
  
  
  bool UfoSmallSymExec::isTracked (const Value &v) 
  {
    // -- shadow values represent memory regions
    // -- only track them when memory is tracked
    if (isShadowMem (v)) return m_trackLvl >= MEM;
    // -- a pointer
    if (v.getType ()->isPointerTy ()) return m_trackLvl >= PTR;
    
    // -- always track integer registers
    return v.getType ()->isIntegerTy ();
  }
  
  Expr UfoSmallSymExec::lookup (SymStore &s, const Value &v)
  {
    Expr u = symb (v);
    // if u is defined it is either an fapp or a constant
    if (u) return bind::isFapp (u) ? s.read (u) : u;
    return Expr (0);
  }

  void UfoSmallSymExec::execEdg (SymStore &s, const BasicBlock &src,
                                 const BasicBlock &dst, ExprVector &side)
  {
    exec (s, src, side, trueE);
    execBr (s, src, dst, side, trueE);
    execPhi (s, dst, src, side, trueE);
    
    // an edge into a basic block that does not return includes the block itself
    const TerminatorInst *term = dst.getTerminator ();
    if (term && isa<const UnreachableInst> (term)) exec (s, dst, side, trueE);
  }
  
  void UfoSmallSymExec::execBr (SymStore &s, const BasicBlock &src, const BasicBlock &dst, 
                                ExprVector &side, Expr act)
  {
    // the branch condition
    if (const BranchInst *br = dyn_cast<const BranchInst> (src.getTerminator ()))
    {
      if (br->isConditional ())
      {
        const Value &c = *br->getCondition ();
        if (const ConstantInt *ci = dyn_cast<const ConstantInt> (&c))
        {
          if ((ci->isOne () && br->getSuccessor (0) != &dst) ||
              (ci->isZero () && br->getSuccessor (1) != &dst))
          {
            side.clear ();
            side.push_back (boolop::limp (act, s.read (errorFlag (src))));
          }
        }
        else if (Expr target = lookup (s, c))
        {
          
          Expr cond = br->getSuccessor (0) == &dst ? target : mk<NEG> (target);
          cond = boolop::lor (s.read (errorFlag (src)), cond);
          cond = boolop::limp (act, cond);
          side.push_back (cond);
        }
        
            
      }
    }   
  }
  
  void UfoLargeSymExec::execCpEdg (SymStore &s, const CpEdge &edge, 
                                   ExprVector &side)
  {
    const CutPoint &target = edge.target ();
    
    bool first = true;
    for (const BasicBlock& bb : edge) 
    {
      if (first)
      {
        s.havoc (m_sem.symb (bb));
        m_sem.exec (s, bb, side, trueE);  
      }
      else execEdgBb (s, edge, bb, side);
      first = false;
    }
    
    execEdgBb (s, edge, target.bb (), side, true);
  }
  
  namespace sem_detail
  {
    struct FwdReachPred : public std::unary_function<const BasicBlock&,bool>
    {
      const CutPointGraph &m_cpg;
      const CutPoint &m_cp;
      
      FwdReachPred (const CutPointGraph &cpg, const CutPoint &cp) : 
        m_cpg (cpg), m_cp (cp) {}
      
      bool operator() (const BasicBlock &bb) const 
      {return m_cpg.isFwdReach (m_cp, bb);}
      bool operator() (const BasicBlock *bb) const
      {return this->operator() (*bb);} 
    };
  }
  
  void UfoLargeSymExec::execEdgBb (SymStore &s, const CpEdge &edge, 
                                   const BasicBlock &bb, 
                                   ExprVector &side, bool last)
  {
    ExprVector edges;
    
    if (last) assert (&bb == &(edge.target ().bb ()));
    
    // -- predicate for reachable from source
    sem_detail::FwdReachPred reachable (edge.parent (), edge.source ());
    
    // compute predecessors, relative to the source cut-point
    llvm::SmallVector<const BasicBlock*, 4> preds;
    for (const BasicBlock* p : seahorn::preds (bb)) 
      if (reachable (p)) preds.push_back (p);
    
    // -- compute source of all the edges
    for (const BasicBlock *pred : preds)
      edges.push_back (s.read (m_sem.symb (*pred)));
      
    // -- update constant representing current bb
    Expr bbV = s.havoc (m_sem.symb (bb));
    // -- update destination of all the edges
    // -- b_i & e_{i,j}
    for (Expr &e : edges) e = mk<AND> (e, bind::boolConst (mk<TUPLE> (e, bbV)));
     

    // -- encode control flow
    // -- b_i -> (b1 & e_{1,i} | b2 & e_{2,i} | ...)
    if (!preds.empty ())
      side.push_back (mk<IMPL> (bbV, 
                                mknary<OR> 
                                (mk<FALSE> (m_sem.getExprFactory ()), edges)));
      
    // unique node with no successors is asserted to always be reachable
    if (last) side.push_back (bbV);
      
    /// -- generate constraints from the phi-nodes (keep them separate for now)
    std::vector<ExprVector> phiConstraints (preds.size ());
    
    unsigned idx = 0;
    for (const BasicBlock *pred : preds)
    {
      // clone s
      SymStore es(s);
        
      // edge_ij -> phi_ij, 
      // -- branch condition
      m_sem.execBr (es, *pred, bb, side, edges[idx]);
      // -- definition of phi nodes
      m_sem.execPhi (es, bb, *pred, side, edges[idx]);
      s.uses (es.uses ());
        
        
      for (const Instruction &inst : bb)
      {
        if (!isa<PHINode> (&inst)) break;
        if (!m_sem.isTracked (inst)) continue;
        
        phiConstraints [idx].push_back (es.read (m_sem.symb (inst)));
      }
      
      idx++;
    }
      
    // create new values for phi-node variables
    ExprVector newPhi;
    for (const Instruction &inst : bb)
    {
      if (!isa<PHINode> (inst)) break;
      if (!m_sem.isTracked (inst)) continue;
      newPhi.push_back (s.havoc (m_sem.symb (inst)));
    }
      
    // connect new phi-node variables with constructed phi-node constraints
    for (unsigned j = 0; j < edges.size (); ++j)
      for (unsigned i = 0; i < newPhi.size (); ++i)
        side.push_back (boolop::limp (edges[j], mk<EQ> (newPhi [i], 
                                                        phiConstraints[j][i])));
        
      
    // actions of the block. The side-conditions are not guarded by
    // the basic-block variable because it does not matter.
    if (!last)
      m_sem.exec (s, bb, side, bbV);
    else if (const TerminatorInst *term = bb.getTerminator ())
      if (isa<UnreachableInst> (term)) m_sem.exec (s, bb, side, trueE);
    
    
     
  }
    
    // 1. execute all basic blocks using small-step semantics in topological order
    
    
    // 2. when a block executes, it updates a special variable for the block
    
    // 3. allocate a Boolean variable for each edge: these are unique
    // if named using bb variables
    
    // 4. side condition: edge -> branchCond & execPhi  
    
    // actions: optionally conditional on the block
    // bb_i -> e_i1 | e_i2 | e_i3
    // e_i1 -> bb_1
    // e_i1 -> brcond (i, 1)
    // e_i1 -> phi_1(i)
}
