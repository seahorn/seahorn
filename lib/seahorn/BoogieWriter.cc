/** 
 * Translate LLVM bitcode into Boogie.
 * 
 * Limitations:
 * - Translate only integer operands. 
 * - All integer operands are treated with unlimited precision.
 *
**/

#include "seahorn/config.h"
#include "seahorn/Transforms/Utils/NameValues.hh"
#include "seahorn/Support/CFG.hh"

#ifdef HAVE_CLAM
#include "seahorn/Analysis/CutPointGraph.hh"
#include "clam/Clam.hh"
#include "clam/AbstractDomain.hh"
#endif

#include "llvm/ADT/DenseMap.h"
#include "llvm/IR/BasicBlock.h"
#include "llvm/IR/Function.h"
#include "llvm/IR/InstVisitor.h"
#include "llvm/Analysis/TargetLibraryInfo.h"
#include "llvm/Pass.h"
#include "llvm/Support/CommandLine.h"
#include "llvm/Support/Debug.h"
#include "llvm/Support/raw_ostream.h"
#include "llvm/Support/ErrorHandling.h"

#include "boost/unordered_map.hpp"
#include "boost/unordered_set.hpp"
#include "boost/optional.hpp"
#include "boost/range/iterator_range.hpp"

namespace seahorn
{
  // main class
  class BoogieWriter {
    llvm::Function &m_func;
    const llvm::DataLayout *m_dl;
    const llvm::TargetLibraryInfo *m_tli;
    const DenseMap<const BasicBlock*, std::string> &m_invariants;
    
   public:
    
    BoogieWriter(llvm::Function &m,
		 const DenseMap<const BasicBlock*, std::string> &invariants,
		 const llvm::DataLayout *dl, const llvm::TargetLibraryInfo *tli);
    
    template<typename Out> Out &write (Out &out);
  }; 
}

/** llvm helpers  **/
namespace llvm {
  static void normalizeCmpInst(CmpInst &I) {
    switch (I.getPredicate()){
    case ICmpInst::ICMP_UGT:	
    case ICmpInst::ICMP_SGT: I.swapOperands(); break; 
    case ICmpInst::ICMP_UGE:	
    case ICmpInst::ICMP_SGE: I.swapOperands(); break; 
    default:;
    }
  }
  static bool isBool(const Type *t)
  { return (t->isIntegerTy(1)); }
  static bool isBool(const Value&v)
  { return isBool(v.getType()); }
  static bool isInteger(const Type *t)
  { return (t->isIntegerTy() && !isBool(t)); }
  static bool isInteger(const Value&v)
  { return isInteger(v.getType()); }
  static boost::optional<int64_t> getIntConstant(const ConstantInt* CI){
    if (CI->getType ()->isIntegerTy(1)) {
      return (int64_t) CI->getZExtValue();
    }
    else if (CI->getValue().getMinSignedBits() <= 64) {
      return CI->getSExtValue();
    }
    else {
      llvm::errs () << "Warning: " << *CI << " does not fit in int64_t.";
      return boost::optional<int64_t>();
    }
  }
  static bool isIntToBool(const CastInst &I)
  { return (isa<TruncInst>(I) && I.getDestTy()->isIntegerTy(1)); }
  static bool isBoolToInt(const CastInst &I)
  { return ((isa<ZExtInst>(I) || isa<SExtInst>(I))  && I.getSrcTy()->isIntegerTy(1)); }
  static bool isAssertFn(const Function* F)
  { return (F->getName().equals("verifier.assert")); }
  static bool isErrorFn(const Function* F) {
    return (F->getName().equals("seahorn.fail") ||
	    F->getName().equals("seahorn.error") ||
	    F->getName().equals("verifier.error") ||
	    F->getName().equals("__VERIFIER_error") || 	    	    
            F->getName().equals("__SEAHORN_error"));
  }
  static bool isAssumeFn(const Function* F)
  { return (F->getName().equals("verifier.assume")); }
  static bool isNotAssumeFn(const Function* F)
  { return (F->getName().equals("verifier.assume.not")); }
  static bool isVerifierCall (const Function *F) {
    return (isAssertFn (F) || isErrorFn (F) ||
	    isAssumeFn(F) || isNotAssumeFn (F));
  }
} // end namespace llvm

using namespace llvm;

namespace seahorn
{

  typedef std::string instruction_t;
  typedef std::string term_t;
  typedef std::string type_t;  

  /** Factory to create boogie instructions **/
  class instruction_factory {
  public:
    
    typedef boost::optional<term_t>  opt_term_t;
    typedef boost::optional<type_t>  opt_type_t;    

  private:

    // map Value to term
    typedef DenseMap<const Value*, term_t> term_cache_t;    
    term_cache_t m_term_cache;
    // create unique term names
    unsigned m_id;
    // reserved term names
    boost::unordered_set<std::string> m_reserved_names;
    
  public:

    typedef term_cache_t::iterator term_iterator_t;
    typedef term_cache_t::const_iterator term_const_iterator_t;    
    
    instruction_factory();

    static bool is_tracked (const Type* ty);
    static bool is_tracked (const Value &v);
    opt_term_t get_value(const Value &v);
    term_t mk_term(std::string prefix = "");
    opt_type_t get_type(const Type* ty);
    opt_type_t get_type(const Value& v);
    
    instruction_t mk_binary_operator(BinaryOperator &I);
    instruction_t mk_assign(CmpInst &I);
    instruction_t mk_cast(CastInst &I);
    instruction_t mk_select(SelectInst &I);
    instruction_t mk_assign(term_t lhs, term_t rhs);
    instruction_t mk_assert(term_t v);
    instruction_t mk_invariant(term_t v);
    instruction_t mk_ite(term_t lhs, term_t cond, term_t v1, term_t v2);
    instruction_t mk_assume(term_t v, bool is_negated);
    instruction_t mk_havoc(term_t v) ;
    instruction_t mk_return();
    instruction_t mk_unreachable();
    instruction_t mk_error();    
    instruction_t mk_call(CallSite CS);
    static instruction_t mk_nop();

    // iterate over cached terms
    term_iterator_t terms_begin() { return m_term_cache.begin();}
    term_iterator_t terms_end() { return m_term_cache.end();}
    term_const_iterator_t terms_begin() const { return m_term_cache.begin();}
    term_const_iterator_t terms_end() const { return m_term_cache.end();}        
  };
  
  instruction_factory::instruction_factory(): m_id(0) {
    m_reserved_names.insert("#SEA_res");
  }
  
  bool instruction_factory::is_tracked (const Type* ty) {
    return (isBool(ty) || isInteger(ty));
  }
  
  bool instruction_factory::is_tracked (const Value &v) {
    // -- ignore any shadow variable created by seahorn
    if (v.getName().startswith ("shadow.mem")) 
      return false;
    return is_tracked(v.getType ());
  }
  
  instruction_factory::opt_term_t instruction_factory::get_value(const Value &v){
    auto it = m_term_cache.find(&v);
    if (it != m_term_cache.end ()) return it->second;
    
    if (is_tracked(v)) {
      if (const llvm::ConstantInt *c = llvm::dyn_cast<const llvm::ConstantInt>(&v)) {
	if (boost::optional<int64_t> n = getIntConstant(c)) {
	  term_t tv;
	  if (isBool(v)) {
	    if (*n == 0) tv = "false";
	    else if (*n == 1) tv = "true";
	    else report_fatal_error("Boolean constant can only be 0 or 1");
	  } else  {
	    tv = std::to_string(*n);
	  }
	  return opt_term_t(tv);
	}
	} else if (!llvm::isa<llvm::ConstantExpr>(v)) {
	term_t tv;
	if (v.hasName())  {
	  if (m_reserved_names.find(v.getName()) != m_reserved_names.end()) {
	    report_fatal_error(v.getName() + " is a reserved named.");
	  }
	  tv = v.getName().str();
	} else {
	  tv = mk_term();
	}
	m_term_cache.insert(std::make_pair(&v, tv));	
	return opt_term_t(tv);
      }
    }
    return opt_term_t();
  }
  
  term_t instruction_factory::mk_term(std::string prefix) {
    if (prefix == "") prefix = std::string("##SEAVAR##");
    ++m_id;
    std::string id_str = std::to_string(m_id);
    return prefix + id_str;
  }
  
  instruction_factory::opt_type_t instruction_factory::get_type(const Type* ty) {
    if (isBool(ty))
      return type_t("bool");
    else if (isInteger(ty))
      return type_t("int");
    else
      return opt_type_t();
  }
  
  instruction_factory::opt_type_t instruction_factory::get_type(const Value& v) {
    return get_type(v.getType());
  }
  
  instruction_t instruction_factory::mk_binary_operator(BinaryOperator &I) {
    // FIXME: consider bitwidth-aware operators
    assert(is_tracked(I));
    
    opt_term_t lhs = get_value(I);
    opt_term_t op1 = get_value(*(I.getOperand(0)));
    opt_term_t op2 = get_value(*(I.getOperand(1)));
    
    if (lhs && op1 && op2) {
      switch (I.getOpcode()) {
      case BinaryOperator::Add:
	return *lhs + " := " + *op1 + " + " + *op2 + ";" ;
      case BinaryOperator::Sub:
	return *lhs + " := " + *op1 + " - " + *op2 + ";" ;	
	case BinaryOperator::Mul:
	  return *lhs + " := " + *op1 + " * " + *op2 + ";" ;		
      case BinaryOperator::SDiv:
	return *lhs + " := " + *op1 + " / " + *op2 + ";" ;			
      case BinaryOperator::SRem:
	return *lhs + " := " + *op1 + " % " + *op2 + ";" ;
	/* begin TODO */
      case BinaryOperator::URem:
      case BinaryOperator::UDiv:
      case BinaryOperator::Shl:
      case BinaryOperator::AShr:
      case BinaryOperator::LShr:
	/* end TODO */
      case BinaryOperator::And:
	return *lhs + " := " + *op1 + " && " + *op2 + ";" ;		
      case BinaryOperator::Or:
	return *lhs + " := " + *op1 + " || " + *op2 + ";" ;
      case BinaryOperator::Xor:
	// TODO: don't know which is the boogie operator
	//return *lhs + " := " + *op1 + " ^  " + *op2 + ";" ;			
      default:;;
	break;				
      }
    }
    errs () << "Boogie translation skipped " << I << "\n";	
    return mk_havoc(*lhs);
  }

  instruction_t mk_if_then_else(term_t cond, term_t then_t, term_t else_t) {
    return "if (" + cond + ") {" + then_t + "} else { " + else_t + "}";
  }

  term_t mk_pos_cst(term_t v) {
    return v + " > 0";
  }
  
  instruction_t instruction_factory::mk_assign(CmpInst &I) {
    // FIXME: consider bitwidth-aware operators    
    assert(is_tracked(I));
    
    normalizeCmpInst(I);
    const Value& v0 = *I.getOperand(0);
    const Value& v1 = *I.getOperand(1);
    
    opt_term_t lhs = get_value(I);
    opt_term_t op1  = get_value(v0);
    opt_term_t op2  = get_value(v1);
    
    if (lhs && op1 && op2) {
      switch (I.getPredicate()) {
      case CmpInst::ICMP_EQ:
	return *lhs + " := " + *op1 + " == " + *op2 + ";" ;
      case CmpInst::ICMP_NE:
	return *lhs + " := " + *op1 + " != " + *op2 + ";" ;	  
      case CmpInst::ICMP_ULT:
	/*
	  if (x > 0) {
	    if (y > 0) { lhs:= x < y;} else {lhs := false;}
          } else {
	    if (y > 0) { lhs:= true;} else {lhs:= x < y;}
          } 
	 */
	return mk_if_then_else(mk_pos_cst(*op1),
			       mk_ite(*lhs,
				      mk_pos_cst(*op2),
				      *op1 + " < " + *op2,
				      "false"),
			       mk_ite(*lhs,
				      mk_pos_cst(*op2),
				      "true",
				      *op1 + " < " + *op2));
      case CmpInst::ICMP_SLT:
	return *lhs + " := " + *op1 + " < " + *op2 + ";" ;	  	  
      case CmpInst::ICMP_ULE:
	/*
	  if (x > 0) {
	    if (y > 0) { lhs:= x <= y;} else {lhs := false;}
          } else {
	    if (y > 0) { lhs:= true;} else {lhs:= x <= y;}
          } 
	 */
	return mk_if_then_else(mk_pos_cst(*op1),
			       mk_ite(*lhs,
				      mk_pos_cst(*op2),
				      *op1 + " <= " + *op2,
				      "false"),
			       mk_ite(*lhs,
				      mk_pos_cst(*op2),
				      "true",
				      *op1 + " <= " + *op2));
      case CmpInst::ICMP_SLE:
	return *lhs + " := " + *op1 + " <= " + *op2 + ";" ;	  	  	  
      default: ;;  
      }
    }
    // if v0 and v1 can be pointers 
    return mk_havoc(*lhs);
  }

  instruction_t instruction_factory::mk_ite(term_t lhs, term_t cond, term_t v1, term_t v2) {
    instruction_t res = "if (" + cond + ") "
      + "{ " + lhs + " := " + v1 + "; } else "
      + "{ " + lhs + " := " + v2 + "; }";
    return res;
  }
  
  instruction_t instruction_factory::mk_cast(CastInst &I) {

    opt_term_t dst = get_value(I);
    opt_term_t src = get_value(*I.getOperand(0));
    if (src && dst) {
      if (isIntToBool(I)) {
	return mk_ite(*dst, mk_pos_cst(*src), "true", "false");
      } else if (isBoolToInt(I)) {
	return mk_ite(*dst, *src, "1", "0");
      } else  {
	// FIXME: consider bitwidths
	// integer to integer 
	return mk_assign(*dst, *src);
      }
    } else {
      // this should not happen
      return instruction_factory::mk_nop();
    }
  }

  instruction_t instruction_factory::mk_select(SelectInst &I) {
    opt_term_t lhs = get_value(I);    
    opt_term_t cond = get_value(*I.getCondition());
    opt_term_t v1 = get_value(*I.getTrueValue());
    opt_term_t v2 = get_value(*I.getFalseValue());
    if (lhs && cond && v1 && v2) {
      return mk_ite(*lhs, *cond, *v1, *v2);
    } else {
      // this should not happen
      return instruction_factory::mk_nop();
    } 
  }
  

  instruction_t instruction_factory::mk_nop(){
    return "";
  }
  
  instruction_t instruction_factory::mk_assign(term_t lhs, term_t rhs)
  { return lhs + " := " + rhs + ";" ; }
  
  instruction_t instruction_factory::mk_assert(term_t v)
  { return "assert " + v + ";" ; }
  
  instruction_t instruction_factory::mk_assume(term_t v, bool is_negated)
  { return std::string("assume ") + (is_negated ? "!" : "") + v + ";" ; }

  instruction_t instruction_factory::mk_havoc(term_t v)
  { return "havoc " + v + ";" ; }

  instruction_t instruction_factory::mk_invariant(term_t v) {
    if (v != "") {
      return "assume " + v + ";" ;
    } else {
      return mk_nop();
    }
  }
  
  instruction_t instruction_factory::mk_return() { return "return;";}    

  instruction_t instruction_factory::mk_unreachable() { return " assume false;";}

  instruction_t instruction_factory::mk_error() { return " assert false;";}
  
  instruction_t instruction_factory::mk_call(CallSite CS) {
    const Value *calleeV = CS.getCalledValue ();
    const Function *callee =dyn_cast<Function>(calleeV);
    assert (callee);
    
    std::vector<term_t> targs;
    for (auto &a: CS.args()) {
      Value *v = a.get();
      //XXX: untracked actual parameters are ignored
      //     this change the arity of the function
      if (instruction_factory::opt_term_t vt = get_value(*v)) {
	targs.push_back(*vt);
      }
    }
    
    instruction_t i("call ");
    // lhs
    Instruction *lhs = CS.getInstruction();
    if (lhs) {
      if (instruction_factory::opt_term_t tlhs = get_value(*lhs)) {
	i  = i + *tlhs + " := ";
      }
    }
    // actual parameters
    i += callee->getName();
    i = i + "(";
    for (std::vector<term_t>::const_iterator it=targs.begin(),et=targs.end(); it!=et; ){
      i = i + *it;
      ++it;
      if (it!=et) i = i + ",";
    }
    i = i + ");";
    return i;
  }
       
  /** internal basic block of boogie instructions **/
  class block {    
  public:
    
    typedef std::string label_t;

  private:
    
    /** llvm basic block associated (it can be null) **/
    const BasicBlock *m_bb; 
    /** name of the block **/    
    std::string m_name;
    /** instructions of the block except goto instruction **/
    std::vector<instruction_t> m_instructions;
    /** goto instruction of the block **/
    std::vector<label_t> m_goto;
    
  public:
    
    block(const BasicBlock *b) : m_bb(b), m_name(b->getName()) {}
    explicit block(std::string name) : m_bb(nullptr), m_name(name) {}
    block() : m_bb(nullptr), m_name("") {}

    label_t get_label() const { return m_name; }

    bool operator==(const block &other) const
    { return m_name == other.m_name; }

    bool operator!=(const block &other) const
    { return !(this->operator==(other)); }

    bool operator<(const block &other) const
    { return m_name < other.m_name; }
    
    void add_instruction(instruction_t inst) { m_instructions.push_back(inst); }

    void operator+=(instruction_t inst) {
      if (!(inst == instruction_factory::mk_nop())) {
	add_instruction(inst);
      }
    }
    
    void add_goto(label_t label) { m_goto.push_back(label); }
    
    template<typename Out>
    Out &write(Out &o) {
      o << m_name << ":\n";
      for (auto i: m_instructions) {
	o << "  " << i << "\n";
      }
      if (!m_goto.empty()) {
	o << "  " << "goto ";
	for (typename std::vector<label_t>::iterator it=m_goto.begin(), et=m_goto.end();
	     it!=et;){
	  o << *it;
	  ++it;
	  if (it != et)
	    o << ",";
	  else
	    o << ";\n";
	}
      }
      return o;
    }
  };

  /** A factory to create boogie basic blocks **/
  class block_factory {
    typedef boost::unordered_map<block::label_t, block> block_map_t;
    
    block_map_t m_bm;
    unsigned m_id;

    block::label_t mk_label(std::string prefix = "") {
      // don't use $bb## because ultimate automizer uses it internally.
      if (prefix == "") prefix = std::string("##SEABLOCK##");
      ++m_id;
      std::string id_str = std::to_string(m_id);
      return prefix + id_str;
    }
    
  public:

    typedef typename block_map_t::iterator iterator;
    typedef typename block_map_t::const_iterator const_iterator;    
    
    block_factory(): m_id(0){}

    block& operator[](block::label_t block_name) {
      return m_bm[block_name];
    }
    
    block& mk_block(const BasicBlock&b) {
      auto res = m_bm.insert(std::make_pair(b.getName(), block(&b)));
      return res.first->second;
    }
    
    block& mk_block(std::string prefix="") {
      block::label_t block_name = mk_label(prefix);
      auto res = m_bm.insert(std::make_pair(block_name, block(block_name)));
      assert (res.second && "block already found");      
      return res.first->second;
    }

    iterator begin(){ return m_bm.begin();}
    iterator end(){ return m_bm.end();}
    const_iterator begin() const { return m_bm.begin();}
    const_iterator end() const { return m_bm.end();}
  };


  /** translate from LLVM to Boogie instruction **/
  class boogieInstVisitor: public InstVisitor<boogieInstVisitor>{
    block &m_bb;
    instruction_factory &m_ifac;
    const DataLayout *m_dl;
    const TargetLibraryInfo *m_tli;
    
  public:
    
    boogieInstVisitor(block &bb,
		      instruction_factory &ifac,
		      const DataLayout *dl, const TargetLibraryInfo *tli)
      : m_bb(bb), m_ifac(ifac), m_dl(dl), m_tli(tli) {}
    
    /// skip PHI nodes (processed elsewhere)
    void visitPHINode (PHINode &I) {}

    /// skip BranchInst (processed elsewhere)
    void visitBranchInst (BranchInst &I) {}

    void visitCmpInst (CmpInst &I) {
      if (m_ifac.is_tracked(I)) {
	m_bb += m_ifac.mk_assign(I);
      }
    }

    void visitBinaryOperator(BinaryOperator &I) {
      if (m_ifac.is_tracked(I)) {
	m_bb += m_ifac.mk_binary_operator(I);
      }
    }
    
    void visitCastInst (CastInst &I) {
      if (m_ifac.is_tracked(I)) {
	m_bb += m_ifac.mk_cast(I);       
      }
    }

    void visitSelectInst (SelectInst &I) {
      if (m_ifac.is_tracked(I)) {
	m_bb += m_ifac.mk_select(I);
      }
    }
    
    void visitCallInst (CallInst &I) {
      CallSite CS (&I);
      const Value *calleeV = CS.getCalledValue ();
      const Function *callee =dyn_cast<Function>(calleeV);
      if (!callee) {         
	if (I.isInlineAsm()) {
	  // -- inline asm: do nothing
	} else {
	  // -- unresolved call
	  errs () << "Boogie translation skipped indirect call. Enable --devirt-functions";
	  if (instruction_factory::opt_term_t vt = m_ifac.get_value(I)) {
	    m_bb += m_ifac.mk_havoc(*vt);
	  }
	}
      } else {
	// -- direct call
	if (isAssertFn(callee) || isAssumeFn(callee) || isNotAssumeFn(callee)) {
	  Value &c = *(CS.getArgument(0));
	  if (instruction_factory::opt_term_t tc = m_ifac.get_value(c)) {
	    if (isAssertFn(callee))
	      m_bb += m_ifac.mk_assert(*tc);
	    else if (isAssumeFn(callee))
	      m_bb += m_ifac.mk_assume(*tc, false);
	    else if (isNotAssumeFn(callee))
	      m_bb += m_ifac.mk_assume(*tc, true);
	  }
	} else if (isErrorFn(callee)) {
	  m_bb += m_ifac.mk_error();
	} else {
	  // -- ignore shadow memory functions created by seahorn
	  if (!callee->getName().startswith ("shadow.mem"))
	    m_bb += m_ifac.mk_call(CS);
	}
      }
    }

    void visitReturnInst (ReturnInst &I) {
      if (Value *RV = I.getReturnValue()) {
	if (instruction_factory::opt_term_t tr = m_ifac.get_value(*RV)) {
	  term_t res("#SEA_res");
	  m_bb += m_ifac.mk_assign(res, *tr);
	}
      }
      
      m_bb += m_ifac.mk_return();
    }
    
    void visitUnreachableInst (UnreachableInst &I) {
      m_bb += m_ifac.mk_unreachable();
    }
    
    void visitGetElementPtrInst (GetElementPtrInst &I) {}
    void visitStoreInst (StoreInst &I) {}    
    void visitLoadInst (LoadInst &I) {
      if (instruction_factory::opt_term_t t = m_ifac.get_value(I))
	m_bb += m_ifac.mk_havoc(*t);
    }
    void visitAllocaInst (AllocaInst &I) {
      if (instruction_factory::opt_term_t t = m_ifac.get_value(I))
	m_bb += m_ifac.mk_havoc(*t);
    }

    /// base case. if all else fails.
    void visitInstruction (Instruction &I) {
      if (m_ifac.is_tracked(I)) {
	errs () << "Boogie translation skipped " << I << "\n";
      }
    }    
    
  };

  /** Translate LLVM PHI instructions **/
  struct boogiePhiVisitor : public InstVisitor<boogiePhiVisitor> {

    // block where assignment will be inserted
    block &m_bb;
    // incoming block of the PHI instruction
    const BasicBlock& m_inc_BB;
    // instruction factory
    instruction_factory &m_ifac;

    boogiePhiVisitor (block &bb, const BasicBlock &inc_BB,
		    instruction_factory &ifac)
      : m_bb(bb), m_inc_BB(inc_BB), m_ifac(ifac) {} 
      
    void visitBasicBlock (BasicBlock &BB) {
      auto curr = BB.begin ();
      if (!isa<PHINode> (curr)) return;

      DenseMap<const Value*, term_t> old_val_map;

      // --- All the phi-nodes must be evaluated atomically. This
      //     means that if one phi node v1 has as incoming value
      //     another phi node v2 in the same block then it should take
      //     the v2's old value (i.e., before v2's evaluation).

      for (; PHINode *phi = dyn_cast<PHINode> (curr); ++curr) {        
        const Value &v = *phi->getIncomingValueForBlock (&m_inc_BB);
        if (!m_ifac.is_tracked(v)) continue;
	
        const PHINode* phi_v = dyn_cast<PHINode> (&v);
        if (phi_v && (phi_v->getParent () == &BB)) {
	  // -- save the old version of the variable that maps to the phi node v
	  assert (v.hasName());
	  auto it = old_val_map.find(&v);
	  if (it == old_val_map.end()) {
	    if (instruction_factory::opt_term_t vt = m_ifac.get_value(v)) {
	      term_t old_val(m_ifac.mk_term());
	      m_bb += m_ifac.mk_assign(old_val, *vt);
	      old_val_map.insert (std::make_pair(&v, old_val));
	    }
	  }
	}
      }

      curr = BB.begin ();
      for (; isa<PHINode> (curr); ++curr) {
        PHINode &phi = *cast<PHINode> (curr);
        if (!m_ifac.is_tracked(phi)) continue;
	instruction_factory::opt_term_t lhs = m_ifac.get_value(phi);
	if (!lhs) continue; // this should not happen
	
        const Value &v = *phi.getIncomingValueForBlock (&m_inc_BB);
        auto it = old_val_map.find (&v);
        if (it != old_val_map.end ()) {
	  // -- use old version if exists
	  m_bb += m_ifac.mk_assign(*lhs, it->second);
        } else {
	  if (instruction_factory::opt_term_t vt = m_ifac.get_value(v)) {
	    m_bb += m_ifac.mk_assign(*lhs, *vt);
	  } else {
	    m_bb += m_ifac.mk_havoc(*lhs);
	  }
	}
      }
    }
  };
  
  BoogieWriter::BoogieWriter(Function &func,
			     const DenseMap<const BasicBlock*, std::string> &invariants,
			     const DataLayout *dl, const TargetLibraryInfo *tli)
    : m_func(func), m_invariants(invariants), m_dl(dl), m_tli(tli) {}

  struct is_formal_argument : std::unary_function<llvm::Argument&, bool> {
    const Value &m_v;
    is_formal_argument(const Value &v): m_v(v) {}
    bool operator()(llvm::Value &a) const {
      return (&a == &m_v);
    }
  };

  template<typename Out, typename TArgs>
  static void write_prototype(Out &out,
			      std::string kind, Function &func, const TArgs &targs,
			      instruction_factory &ifac) {
    
    out << kind << " " << func.getName() << "(";
    for (typename TArgs::const_iterator it=targs.begin(),et=targs.end();it!=et;){
      out << (*it).first << " : " << (*it).second;
      ++it;
      if (it!=et) out << ",";
    }
    out << ") returns (";
    if (instruction_factory::opt_type_t ty = ifac.get_type(func.getReturnType()))
      out << "#SEA_res" << " : " << *ty;
    out << ")";
  }
  
  template<typename Out>
  Out &BoogieWriter::write(Out &out) {

    /** the block factory **/
    block_factory bfac;
    /** the instruction factory **/
    instruction_factory ifac;
    
    // -- create a block for each llvm basic block
    for (auto &BB: m_func) {
      block& b = bfac.mk_block(BB);
      // -- if there are available invariants we add them.
      auto it = m_invariants.find(&BB);
      if (it != m_invariants.end()) {
      	b += ifac.mk_invariant(term_t(it->second));
      }
    }

    // -- process the cfg
    for (auto &cur : m_func) {
      // translate the block ignoring branches and phi-nodes
      block &gcur = bfac[cur.getName()];	  
      boogieInstVisitor v(gcur, ifac, m_dl, m_tli);
      v.visit(&cur);
      
      for (const BasicBlock *dst : succs (cur)) {
	
	block *gmid = nullptr;
	
	if (const BranchInst *br = dyn_cast<const BranchInst>(cur.getTerminator())) {
	  block &gdst = bfac[dst->getName()];	    
	  if (br->isConditional()) {
	    // -- move branch condition in cur to a new block,
	    //    called mid, inserted between bb and dst
	    gmid = &(bfac.mk_block());
	    
	    gcur.add_goto(gmid->get_label());
	    gmid->add_goto(gdst.get_label());
	    
	    if (instruction_factory::opt_term_t tc = ifac.get_value(*br->getCondition ())) {
	      bool is_negated = (br->getSuccessor (1) == dst);
	      *gmid += ifac.mk_assume(*tc, is_negated);		
	    }
	  } else {
	    gcur.add_goto(gdst.get_label());
	  }
	}
	
	// -- phi nodes in dst are translated into assignments in
	//   the predecessor
	boogiePhiVisitor v((gmid ? *gmid : gcur), cur, ifac);
	v.visit(const_cast<BasicBlock &>(*dst));
      }
    }
    
    // Collect tracked formal parameters
    typedef std::vector<std::pair<term_t,type_t> > formal_params_t;
    formal_params_t targs;
    for (Value &a: m_func.args()) {
      //XXX: untracked formal parameters are ignored
      //     this change the arity of the function
      if (!ifac.is_tracked(a)) continue;
      instruction_factory::opt_term_t ta  = ifac.get_value(a);
      instruction_factory::opt_term_t tty = ifac.get_type(a);
      if (ta && tty) {
	targs.push_back(std::make_pair(*ta,*tty));
      }
    }

    // procedure definition
    write_prototype(out, "procedure", m_func, targs, ifac);
    out << ";\n";

    // implementation definition for non-declaration/non-intrinsic functions
    if (!m_func.isDeclaration() && !m_func.isIntrinsic()) {
      write_prototype(out, "implementation", m_func, targs, ifac);
      out << "{\n";
      // local var definitions
      for (auto &kv: boost::make_iterator_range(ifac.terms_begin(), ifac.terms_end())) {
	is_formal_argument ifa (*(kv.first));
	if (std::find_if(m_func.arg_begin(), m_func.arg_end(), ifa) == m_func.arg_end()) {
	  // only local variables
	  instruction_factory::opt_type_t ty = ifac.get_type(*(kv.first));
	  assert(ty);
	  out << "  var " << kv.second << " : " << *ty << ";\n";
	}
      }
      // basic blocks (make sure we write first the entry block)
      block &entry = bfac[m_func.getEntryBlock().getName()];
      entry.write(out);
      for (auto &kv: boost::make_iterator_range(bfac.begin(), bfac.end())) {
	if (kv.first == m_func.getEntryBlock().getName())
	  continue;
	kv.second.write(out);
      }
      out << "}\n";
    }
    
    return out;
  }

  class BoogieWriterPass: public ModulePass {
    // output stream for the boogie program
    raw_ostream *m_out;

    const TargetLibraryInfo *m_tli;
    const DataLayout *m_dl;
    bool m_use_crab;    
    #ifdef HAVE_CLAM
    clam::ClamPass *m_crab;

    static const Value* is_bool_cst (clam::lin_cst_t cst) {
      if (cst.is_disequation ()) return nullptr;
      auto e = cst.expression() - cst.expression().constant();
      if (std::distance (e.begin (), e.end ()) != 1) return nullptr; 
      auto t = *(e.begin ());
      auto v = t.second.name();
      if (!(v.get()))
	return nullptr;
      if ( (*(v.get ()))->getType ()->isIntegerTy (1))
	return *(v.get ()); 
      else 
	return nullptr; 
    }
    #endif     
  public:
    
    static char ID;

    BoogieWriterPass(raw_ostream *out = &llvm::errs(), bool use_crab = false)
      : ModulePass(ID), m_out(out),
	m_tli(nullptr), m_dl(nullptr),
	m_use_crab(use_crab)
      #ifdef HAVE_CLAM
      , m_crab(nullptr)
      #endif
    {}

    virtual bool runOnModule (Module &M) {
      m_tli = &getAnalysis<TargetLibraryInfoWrapperPass>().getTLI();
      m_dl = &(M.getDataLayout());

      *m_out << "// Boogie program generated by SeaHorn.\n";
      
      #ifdef HAVE_CLAM
      if (m_use_crab) {
	m_crab = &getAnalysis<clam::ClamPass> ();
	std::string absdom = m_crab->get_analysis_params().abs_dom_to_str();
	*m_out << "// Used Crab to add invariants using the domain: " << absdom << "\n\n";
      }
      #endif 
     
      for (Function &F : M) {
	// -- ignore shadow memory functions created by seahorn
	if (F.getName().startswith ("shadow.mem")) continue;
        runOnFunction (F);
      }
      return false;
    }
    
    #ifdef HAVE_CLAM
    // some tweaks to adapt crab pretty printing format to boogie
    template<typename Out>
    void translate_crab_invariant (Out& out, clam::lin_cst_t cst) {
      assert(!cst.is_tautology());
      
      if (cst.is_contradiction()) {
	out << "false";
      } else {	  
	if (cst.is_equality()) {
	  // FIXME: crab prints equalities with "="
	  clam::lin_exp_t e = cst.expression() - cst.constant();
	  ikos::z_number c = -(cst.constant());
	  out << e << " == " << c;
	} else {
	  cst.write(out);
	}      
      }
    }
    #endif 
    
    bool runOnFunction(Function &F){
      
      DenseMap<const BasicBlock*, std::string> invariants;
      
      #ifdef HAVE_CLAM
      if (m_crab) {
	// FIXME: some crash happens when cpg is used.
	//const CutPointGraph &cpg = getAnalysis<CutPointGraph>(F);
	for (auto &B: F) {
	  // if (!cpg.isCutPoint(B)) {
	  //   continue;
	  // }
      	  if (auto dom_ptr = m_crab->get_pre(&B)) {
      	    crab::crab_string_os out;
	    clam::lin_cst_sys_t csts = dom_ptr->to_linear_constraints();
	    typename clam::lin_cst_sys_t::iterator it = csts.begin();
	    typename clam::lin_cst_sys_t::iterator et = csts.end();
	    for (; it!=et; ) {
	      clam::lin_cst_t cst = *it;
	      if (cst.is_tautology() || is_bool_cst(cst)) {
		// TODO: translate constraints with boolean operands
		// do nothing
		++it;
		continue;
	      } else {
		translate_crab_invariant(out, cst);
	      }
	      ++it;
	      if (it != et) {
		out << " && ";
	      } 
	    }
      	    invariants[&B] = out.str();
      	  }
	}
      }
      #endif 
      BoogieWriter writer(F, invariants, m_dl, m_tli);
      writer.write(*m_out);
      
      return false;
    }
    
    virtual StringRef getPassName() const {
      return "Translate LLVM bitcode to Boogie";
    }
    
    virtual void getAnalysisUsage(AnalysisUsage &AU) const {
      AU.setPreservesAll();
      
      AU.addRequired<TargetLibraryInfoWrapperPass>();
      AU.addRequired<seahorn::NameValues>();
      
      #ifdef HAVE_CLAM
      AU.addRequired<seahorn::TopologicalOrder>();      
      AU.addRequired<CutPointGraph>();
      AU.addRequired<clam::ClamPass>();
      
      #endif 
    }
  };


  char BoogieWriterPass::ID = 0;
  
  Pass* createBoogieWriterPass (raw_ostream *out, bool use_crab) {
    return new BoogieWriterPass(out, use_crab);
  }
  
} // end namespace seahorn

static llvm::RegisterPass<seahorn::BoogieWriterPass>
X("boogie-writer", "Translate LLVM bitcode to a Boogie program");
