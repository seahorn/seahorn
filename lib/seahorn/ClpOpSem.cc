/// Symbolic execution based on semantics used in CLP
///
/// Most variables are integer except errorFlag and variables
/// originated from basic blocks which are Boolean. This semantics also
/// tries to minimize the number of auxiliary variables.

#include "llvm/IR/GetElementPtrTypeIterator.h"

#include "seahorn/ClpOpSem.hh"
#include "seahorn/Support/CFG.hh"
#include "seahorn/Transforms/Instrumentation/ShadowMemDsa.hh"

#include "seahorn/Expr/ExprLlvm.hh"
#include "seahorn/Support/IteratorExtras.hh"
#include "seahorn/Support/SeaDebug.h"

using namespace seahorn;
using namespace llvm;

namespace
{
  struct SymExecBase
  {
    SymStore &m_s;
    ExprFactory &m_efac;
    ClpOpSem &m_sem;
    ExprVector &m_side;

    Expr trueE;
    Expr falseE;
    Expr zero;
    Expr one;

    /// -- current read memory
    Expr m_inMem;
    /// -- current write memory
    Expr m_outMem;

    /// -- parameters for a function call
    ExprVector m_fparams;

    SymExecBase (SymStore &s, ClpOpSem &sem, ExprVector &side) :
      m_s(s), m_efac (m_s.getExprFactory ()), m_sem (sem), m_side (side)
    {
      trueE  = mk<TRUE> (m_efac);
      falseE = mk<FALSE> (m_efac);
      zero   = mkTerm<expr::mpz_class> (0UL, m_efac);
      one    = mkTerm<expr::mpz_class> (1UL, m_efac);
      // -- first two arguments are reserved for error flag
      m_fparams.push_back (falseE);
      m_fparams.push_back (falseE);
      m_fparams.push_back (falseE);
    }
    Expr symb (const Value &I) {return m_sem.symb (I);}

    Expr read (const Value &v)
    { return m_sem.isTracked (v) ? m_s.read (symb (v)) : Expr (0); }

    Expr lookup (const Value &v) {return m_sem.lookup (m_s, v);}

    Expr havoc (const Value &v)
    {return m_sem.isTracked (v) ? m_s.havoc (symb (v)) : Expr (0);}

    void write (const Value &v, Expr val)
    { if (m_sem.isTracked (v)) m_s.write (symb (v), val); }

    Expr negate (Expr e)
    { return op::boolop::nnf (boolop::lneg (e)); }

  };

  struct SymExecVisitor : public InstVisitor<SymExecVisitor>,
                          SymExecBase
  {
    SymExecVisitor (SymStore &s, ClpOpSem &sem, ExprVector &side) :
      SymExecBase (s, sem, side) {}

    /// base case. if all else fails.
    void visitInstruction (Instruction &I) {havoc (I);}

    /// skip PHI nodes
    void visitPHINode (PHINode &I) { /* do nothing */ }


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
        res = mk<EQ>(op0,op1);
        break;
      case CmpInst::ICMP_NE:
        res = mk<NEQ>(op0,op1);
        break;
      case CmpInst::ICMP_UGT:
      case CmpInst::ICMP_SGT:
        res = mk<GT>(op0,op1);
        break;
      case CmpInst::ICMP_UGE:
      case CmpInst::ICMP_SGE:
        res = mk<GEQ>(op0,op1);
        break;
      case CmpInst::ICMP_ULT:
      case CmpInst::ICMP_SLT:
        res = mk<LT>(op0,op1);
        break;
      case CmpInst::ICMP_ULE:
      case CmpInst::ICMP_SLE:
        res = mk<LEQ>(op0,op1);
        break;
      default:
        break;
      }
      if (res) write (I, res);
    }

    void visitSelectInst(SelectInst &I)
    {
      if (!m_sem.isTracked (I)) return;

      Expr lhs = havoc (I);
      Expr cond = lookup (*I.getCondition ());
      Expr op0 = lookup (*I.getTrueValue ());
      Expr op1 = lookup (*I.getFalseValue ());


      if (cond && op0 && op1)
      {
        m_side.push_back (mk<OR> (mk<AND> (cond, mk<EQ>(lhs, op0)),
                                  mk<AND> (negate (cond), mk<EQ> (lhs, op1))));
      }
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
        doArithmetic (lhs, I);
        break;

      case BinaryOperator::And:
      case BinaryOperator::Or:
      case BinaryOperator::Xor:
      case BinaryOperator::AShr:
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

      if (bind::isBoolConst (op0) || bind::isIntConst (op0))
      { op0 = mk<GT>(op0, zero); }

      if (bind::isBoolConst (op1) || bind::isIntConst (op1))
      { op1 = mk<GT>(op1, zero); }

      switch(i.getOpcode())
      {
        case BinaryOperator::And:
          res = boolop::land (op0,op1);
          break;
        case BinaryOperator::Or:
          res = boolop::lor (op0,op1);
          break;
        case BinaryOperator::Xor:
          res = boolop::lor (boolop::land (op0, negate (op1)),
                             boolop::land (negate (op0), op1));
          break;
        default:
          break;
      }

      if (res) write (i, res);
    }

    Expr doLeftShift (Expr op1, const ConstantInt *op2)
    {
      uint64_t shift = op2->getValue().getZExtValue();
      unsigned long factor = 1UL;
      for (unsigned long i = 0; i < shift; ++i) { factor = factor * 2; }
      Expr res = mk<MULT>(op1, mkTerm<expr::mpz_class>(factor, m_efac));
      return res;
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
          res = mk<PLUS>(op1, op2);
          break;
        case BinaryOperator::Sub:
          res = mk<MINUS>(op1, op2);
          break;
        case BinaryOperator::Mul:
          res = mk<MULT>(op1, op2);
          break;
        case BinaryOperator::SDiv:
        case BinaryOperator::UDiv:
          res = mk<DIV>(op1, op2);
          break;
        case BinaryOperator::Shl:
          if (const ConstantInt *ci = dyn_cast<ConstantInt> (&v2))
          {
            res = doLeftShift (op1, ci);
            break;
          }
        default:
          break;
      }
      if (res) write (i, res);
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

      write (I, op0);
    }

    void visitZExtInst (ZExtInst &I) {doExtCast (I);}
    void visitSExtInst (SExtInst &I) {doExtCast (I);}

    void visitGetElementPtrInst (GetElementPtrInst &gep)
    {
      if (!m_sem.isTracked (gep)) return;
      Expr lhs = havoc (gep);

      Expr op = m_sem.ptrArith (m_s, gep);
      if (op) m_side.push_back (mk<EQ> (lhs, op));
    }


    void doExtCast (CastInst &I)
    {
      Expr lhs = havoc (I);
      const Value& v0 = *I.getOperand (0);
      Expr op0 = lookup (v0);

      if (!op0) return;

      if (v0.getType ()->isIntegerTy (1))
      {
        if (const ConstantInt *ci = dyn_cast<ConstantInt> (&v0))
        {
          if (ci->isOne ())
            m_side.push_back (mk<EQ> (lhs, one));
          else
            m_side.push_back (mk<EQ> (lhs, zero));
        }
        else
        {
          m_side.push_back (mk<OR> (mk<AND> (op0, mk<EQ>(lhs, one)),
                                    mk<AND> (negate (op0), mk<EQ> (lhs, zero))));
        }
      }
      else
      { write (I, op0); }
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


      if (F.getName ().equals ("verifier.assume"))
      {
        assert (m_fparams.size () == 3);
        // -- assumption is only active when error flag is false
        m_side.push_back (boolop::lor (m_s.read (m_sem.errorFlag (BB)),
                                       lookup (*CS.getArgument (0))));
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
      else if (F.getName ().equals ("verifier.assume.not"))
      {
        assert (m_fparams.size () == 3);
        m_side.push_back (boolop::lor (m_s.read (m_sem.errorFlag (BB)),
                                       boolop::lneg (lookup (*CS.getArgument (0)))));
      }
      else if (m_sem.hasFunctionInfo (F))
      {
        const FunctionInfo &fi = m_sem.getFunctionInfo (F);

        // enabled
        m_fparams [0] = trueE;
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
      if (m_sem.isTracked (I)) havoc (I);
      // if (!m_inMem || !m_sem.isTracked (I))  return;
      // Expr lhs = havoc (I);
      // Expr op0 = lookup (*I.getPointerOperand ());

      // if (op0)
      // {
      //   Expr rhs = op::array::select (m_inMem, op0);
      //   if (I.getType ()->isIntegerTy (1))
      //     // -- convert to Boolean
      //     rhs = mk<NEQ> (rhs, mkTerm (expr::mpz_class(0), m_efac));

      //   m_side.push_back (mk<EQ> (lhs, rhs));
      // }

      // m_inMem.reset ();
    }

    void visitStoreInst (StoreInst &I)
    {
      // if (!m_inMem || !m_outMem || !m_sem.isTracked (*I.getOperand (0))) return;

      // Expr idx = lookup (*I.getPointerOperand ());
      // Expr v = lookup (*I.getOperand (0));

      // if (v && I.getOperand (0)->getType ()->isIntegerTy (1))
      //   // -- convert to int
      //   v = boolop::lite (v, mkTerm (expr::mpz_class (1), m_efac),
      //                     mkTerm (expr::mpz_class (0), m_efac));

      // if (idx && v)
      //   m_side.push_back (mk<EQ> (m_outMem,
      //                             op::array::store (m_inMem, idx, v)));
      // m_inMem.reset ();
      // m_outMem.reset ();
    }


    void visitCastInst (CastInst &I)
    {
      if (!m_sem.isTracked (I)) return;

      Expr lhs = havoc (I);
      const Value &v0 = *I.getOperand (0);

      Expr u = lookup (v0);
      if (u) write (I, u);
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

    SymExecPhiVisitor (SymStore &s, ClpOpSem &sem,
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
      write (I, op0);
    }

  };
}

namespace seahorn
{
  Expr ClpOpSem::errorFlag (const BasicBlock &BB)
  {
    // -- if BB belongs to a function that cannot fail, errorFlag is always false
    if (m_canFail && !m_canFail->canFail (BB.getParent ())) return falseE;
    return this->LegacyOperationalSemantics::errorFlag (BB);
  }

  void ClpOpSem::exec (SymStore &s, const BasicBlock &bb, ExprVector &side,
                              Expr act)
  {
    assert (isOpX<TRUE> (act));
    SymExecVisitor v(s, *this, side);
    v.visit (const_cast<BasicBlock&>(bb));
  }

  void ClpOpSem::exec (SymStore &s, const Instruction &inst, ExprVector &side)
  {
    SymExecVisitor v (s, *this, side);
    v.visit (const_cast<Instruction&>(inst));
  }


  void ClpOpSem::execPhi (SymStore &s, const BasicBlock &bb,
                                 const BasicBlock &from, ExprVector &side, Expr act)
  {
    assert (isOpX<TRUE> (act));
    SymExecPhiVisitor v(s, *this, side, from);
    v.visit (const_cast<BasicBlock&>(bb));
  }

  Expr ClpOpSem::ptrArith (SymStore &s, GetElementPtrInst& gep) {
    Value& base = *gep.getPointerOperand ();
    Expr res = lookup (s, base);
    if (!res) return res;

    for(auto GTI = gep_type_begin(&gep), GTE = gep_type_end(&gep); GTI != GTE; ++GTI) {
      if (const StructType *st = GTI.getStructTypeOrNull()) {
	if (const ConstantInt *ci = dyn_cast<const ConstantInt>(GTI.getOperand())) {
	  Expr off = mkTerm<expr::mpz_class>((unsigned long)fieldOff(st, ci->getZExtValue()), m_efac);
	  res = mk<PLUS>(res, off);
	} else
	  assert(0);
      } else {
        // otherwise we have a sequential type like an array or vector.
        // Multiply the index by the size of the indexed type.
        Expr sz = mkTerm<expr::mpz_class>((unsigned long)storageSize(GTI.getIndexedType()), m_efac);
        res = mk<PLUS>(res, mk<MULT>(lookup(s, *GTI.getOperand()), sz));
      }
    }
    return res;
  }

  unsigned ClpOpSem::storageSize (const llvm::Type *t)
  {return m_td->getTypeStoreSize (const_cast<Type*> (t));}

  unsigned ClpOpSem::fieldOff (const StructType *t, unsigned field)
  {
    return m_td->getStructLayout (const_cast<StructType*>(t))->getElementOffset (field);
  }

  Expr ClpOpSem::symb (const Value &I)
  {
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
          return c->isOne () ? trueE : falseE;
        expr::mpz_class k = toMpz (c->getValue ());
        return mkTerm<expr::mpz_class> (k, m_efac);
      }
      else if (cv->isNullValue () || isa<ConstantPointerNull> (&I))
        return mkTerm<expr::mpz_class> (0UL, m_efac);
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
            expr::mpz_class k = toMpz (val->getValue ());
            return mkTerm<expr::mpz_class> (k, m_efac);
          }
          // -- strip cast
          else return symb (*ce->getOperand (0));
        }
      }
    }

    // -- everything else is mapped to a constant
    Expr v = mkTerm<const Value*> (&I, m_efac);

    const Value *scalar = nullptr;
    if (m_trackLvl >= MEM && shadow_dsa::isShadowMem (I, &scalar))
    {
      Expr intTy = sort::intTy (m_efac);
      Expr ty = sort::arrayTy (intTy, intTy);
      return bind::mkConst (v, ty);
    }

    if (isTracked (I))
    {
      if (I.getType ()->isIntegerTy (1))
        return bind::boolConst (v);
      else
        return bind::intConst (v);
    }

    return Expr(0);
  }

  const Value &ClpOpSem::conc (Expr v) const
  {
    assert (isOpX<FAPP> (v));
    // name of the app
    Expr u = bind::fname (v);
    // name of the fdecl
    u = bind::fname (u);
    assert (isOpX<VALUE> (v));
    return *getTerm<const Value*> (v);
  }


  bool ClpOpSem::isTracked (const Value &v) const
  {
    const Value* scalar;

    // -- shadow values represent memory regions
    // -- only track them when memory is tracked
    if (shadow_dsa::isShadowMem (v, &scalar)) return m_trackLvl >= MEM;
    // -- a pointer
    if (v.getType ()->isPointerTy ()) return m_trackLvl >= PTR;

    // -- always track integer registers
    return v.getType ()->isIntegerTy ();
  }

  Expr ClpOpSem::lookup (SymStore &s, const Value &v)
  {
    Expr u = symb (v);
    // if u is defined it is either an fapp or a constant
    if (u) return bind::isFapp (u) ? s.read (u) : u;
    return Expr (0);
  }

  void ClpOpSem::execEdg (SymStore &s, const BasicBlock &src,
                                 const BasicBlock &dst, ExprVector &side)
  {
    Expr trueE = mk<TRUE> (m_efac);
    exec (s, src, side, trueE);
    execBr (s, src, dst, side, trueE);
    execPhi (s, dst, src, side, trueE);

    // an edge into a basic block that does not return includes the block itself
    const TerminatorInst *term = dst.getTerminator ();
    if (term && isa<const UnreachableInst> (term)) exec (s, dst, side, trueE);

  }

  void ClpOpSem::execBr (SymStore &s, const BasicBlock &src, const BasicBlock &dst,
                                ExprVector &side, Expr act)
  {
    assert (isOpX<TRUE> (act));
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
            side.push_back (s.read (errorFlag (src)));
          }
        }
        else if (Expr target = lookup (s, c))
        {
          SymExecBase sym (s, *this, side);
          Expr cond = br->getSuccessor (0) == &dst ? target : sym.negate (target);
          cond = boolop::lor (s.read (errorFlag (src)), cond);
          side.push_back (cond);
        }
      }
    }
  }

}
