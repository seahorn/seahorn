#include "seahorn/HornCex.hh"

#include "llvm/IR/Function.h"
#include "ufo/Stats.hh"

#include "boost/range/algorithm/reverse.hpp"

#include "seahorn/HornifyModule.hh"
#include "seahorn/HornSolver.hh"
#include "seahorn/Analysis/CutPointGraph.hh"
#include "seahorn/Analysis/CanFail.hh"

#include "seahorn/Bmc.hh"

#include "boost/range.hpp"
#include "boost/range/adaptor/reversed.hpp"
#include "boost/range/algorithm/sort.hpp"
#include "boost/container/flat_set.hpp"
#include "boost/container/map.hpp"
#include <boost/algorithm/string/predicate.hpp>


#include "llvm/Support/CommandLine.h"
#include "llvm/Support/ToolOutputFile.h"
#include "llvm/Support/FileSystem.h"

#include "llvm/IR/IntrinsicInst.h"
#include "llvm/IR/DebugLoc.h"
#include "llvm/IR/DebugInfo.h"
#include "llvm/IR/GlobalValue.h"
#include "llvm/IR/ValueMap.h"
#include "llvm/IR/IRBuilder.h"
#include "llvm/IR/Verifier.h"

#include "llvm/Bitcode/ReaderWriter.h"

#include <gmpxx.h>

static llvm::cl::opt<std::string>
SvCompCexFile("horn-svcomp-cex", llvm::cl::desc("Counterexample in SV-COMP XML format"),
              llvm::cl::init(""), llvm::cl::value_desc("filename"));

static llvm::cl::opt<std::string>
SvCompCexFileSpec("horn-svcomp-cex-spec", 
                  llvm::cl::desc("Specification key in SV-COMP XML format"),
                  llvm::cl::init("CHECK( init(main()), LTL(G ! call(__VERIFIER_error())) )"));

static llvm::cl::opt<std::string>
SvCompCexFileMemModel("horn-svcomp-cex-mem", 
                      llvm::cl::desc("Memory model key in SV-COMP XML format"),
                      llvm::cl::init("simple"));

static llvm::cl::opt<std::string>
SvCompCexFileArch("horn-svcomp-cex-arch", 
                  llvm::cl::desc("Architecture key in SV-COMP XML format"),
                  llvm::cl::init("32bit"));

static llvm::cl::opt<std::string>
HornCexSmtFilename("horn-cex-smt", llvm::cl::desc("Counterexample validate SMT problem"),
               llvm::cl::init(""), llvm::cl::value_desc("filename"), llvm::cl::Hidden);

static llvm::cl::opt<std::string>
HornCexLLVM("horn-llvm-cex", llvm::cl::desc("Produce detailed counterexample in executable LLVM bitcode format"),
               llvm::cl::init(""), llvm::cl::value_desc("filename"));


using namespace llvm;
namespace seahorn
{
  
  template <typename O> class SvCompCex;
  static void dumpSvCompCex (BmcTrace &trace);
  
  char HornCex::ID = 0;
  
  bool HornCex::runOnModule (Module &M)
  {
    for (Function &F : M)
      if (F.getName ().equals ("main")) return runOnFunction (M, F);
    return false;
  }

  // XXX: Does this belong here?
  // XXX: Support other types of terminals (i.e., boolean)
  static Constant* ufoToLLVM(Type *ty, Expr e) {
    // XXX: I am assuming we will always be given a Terminal expression
    const Terminal<mpz_class> &T = dynamic_cast<const Terminal<mpz_class>&> (e.get()->op());
    return ConstantInt::get(cast<IntegerType> (ty), T.get().get_str(), 10);
  }

  static void writeLLVMHarness(std::string HarnessFilename, Module &M, Function &F, BmcTrace &trace)
  {

    Module Harness("harness", getGlobalContext());

    ValueMap<Function*, ExprVector> FuncValueMap;

    // Look for calls in the trace
    for (unsigned loc = 0; loc < trace.size(); loc++)
    {
      const BasicBlock &BB = *trace.bb(loc);
      for (auto &I : BB)
      {
        if (const CallInst *ci = dyn_cast<CallInst> (&I))
        {
          Function *CF = ci->getCalledFunction ();

          Expr V = trace.eval (loc, I);
          if (!V) continue;

          // If the function name does not have a period in it,
          // we assume it is an original function.
          if (CF->getName().find_first_of('.') == StringRef::npos &&
              CF->isExternalLinkage(CF->getLinkage())) {
            FuncValueMap[CF].push_back(V);
          }
        }
      }
    }

    // Build harness functions
    for (auto CFV : FuncValueMap) {

      auto CF = CFV.first;
      auto& UFOarray = CFV.second;

      // This is where we will build the harness function
      Function *HF = cast<Function> (Harness.getOrInsertFunction(CF->getName(), cast<FunctionType> (CF->getFunctionType())));

      Type *RT = CF->getReturnType();
      ArrayType* AT = ArrayType::get(RT, UFOarray.size());

      // Convert UFO terminals to LLVM constants
      SmallVector<Constant*, 20> LLVMarray;
      std::transform(UFOarray.begin(), UFOarray.end(), std::back_inserter(LLVMarray),
                     [RT](Expr e) { return ufoToLLVM(RT, e); });

      // This is an array containing the values to be returned
      GlobalVariable* CA = new GlobalVariable(Harness,
                                              AT,
                                              true,
                                              GlobalValue::PrivateLinkage,
                                              ConstantArray::get(AT, LLVMarray));

      // Build the body of the harness function
      BasicBlock *BB = BasicBlock::Create(getGlobalContext(), "entry", HF);
      IRBuilder<> Builder(BB);

      Type *CountType = IntegerType::get(getGlobalContext(), 32);
      GlobalVariable* Counter = new GlobalVariable(Harness,
                                                   CountType,
                                                   false,
                                                   GlobalValue::PrivateLinkage,
                                                   ConstantInt::get(CountType, 0));

      Value *LoadCounter = Builder.CreateLoad(Counter);
      Value *ArrayLookup = Builder.CreateLoad(Builder.CreateGEP(CA,
                                                                std::vector<Value*> {
                                                                  ConstantInt::get(CountType, 0),
                                                                    LoadCounter
                                                                    }));

      Builder.CreateStore(Builder.CreateAdd(LoadCounter,
                                            ConstantInt::get(CountType, 1)),
                          Counter);
      Builder.CreateRet(ArrayLookup);
    }

    std::error_code error_code;
    raw_fd_ostream out(HornCexLLVM, error_code, sys::fs::F_None);
    assert (!out.has_error());
    verifyModule(Harness, &errs());
    WriteBitcodeToFile(&Harness, out);
    out.close();
  }

  bool HornCex::runOnFunction (Module &M, Function &F)
  {
    HornSolver &hs = getAnalysis<HornSolver> ();
    // -- only run if result is true, skip if it is false or unknown
    if (hs.getResult ()) ; else return false;

    LOG ("cex", 
         errs () << "Analyzed Function:\n"
         << F << "\n";);

    HornifyModule &hm = getAnalysis<HornifyModule> ();
    const CutPointGraph &cpg = getAnalysis<CutPointGraph> (F);
    
    auto &fp = hs.getZFixedPoint ();
    ExprVector rules;
    fp.getCexRules (rules);
    boost::reverse (rules);
    
    // extract a trace of basic blocks corresponding to the counterexample
    SmallVector<const BasicBlock*, 8> bbTrace;
    SmallVector<const CutPoint*, 8> cpTrace;
    
    // -- all counterexamples start at the entry block of the function
    cpTrace.push_back (&cpg.getCp (F.getEntryBlock ()));
    
    for (Expr r : rules)
    {
      
      // filter away all rules not from main()
      Expr src, dst;

      {
        dst = isOpX<IMPL> (r) ? r->arg (1) : r;
        // -- skip rules whose destinations are not basic blocks
        if (!hm.isBbPredicate (dst)) continue;
        const BasicBlock &bb = hm.predicateBb (dst);
        // -- skip basic blocks of non-main function
        if (bb.getParent () != &F) continue;
      }
      
      if (isOpX<IMPL> (r)) 
      { 
        dst = r->arg (1);
        r = r->arg (0);
        src = isOpX<AND> (r) ? r->arg (0) : r;
      }
      else dst = r;
      if (src && !bind::isFapp (src)) src.reset (0);
      
      // -- if there is a src, then it was dst in previous iteration
      assert (bbTrace.empty () || bbTrace.back () == &hm.predicateBb (src));
      const BasicBlock *bb = &hm.predicateBb (dst);
      
      // XXX sometimes the cex includes the entry block, sometimes it does not
      // XXX normalize by removing it
      if (bb == &F.getEntryBlock ()) continue;
      
      bbTrace.push_back (bb);
      if (cpg.isCutPoint (*bb)) 
      {
        const CutPoint &cp = cpg.getCp (*bb);
        cpTrace.push_back (&cp);
      }
    }
    
    LOG ("cex", 
         errs () << "TRACE BEGIN\n";
         for (auto bb : bbTrace)
         {
           errs () << bb->getName ();
           if (cpg.isCutPoint (*bb)) errs () << " C";
           errs () << "\n";
         }
         errs () << "TRACE END\n";);
    
    // -- release trace resources
    bbTrace.clear ();
    
    // -- create a BMC engine. Use fixed symbolic execution
    // -- semantics. Possibly different than the semantics used by the
    // -- HornSolver
    ExprFactory &efac = hm.getExprFactory ();
    UfoSmallSymExec sem (efac, *this, MEM);
    BmcEngine bmc (sem, hm.getZContext ());
    
    // -- load the trace into the engine
    for (const CutPoint *cp : cpTrace)
      bmc.addCutPoint (*cp);
    
    // -- construct BMC instance
    bmc.encode ();

    if (!HornCexSmtFilename.empty ())
    {
      std::error_code EC;
      raw_fd_ostream file (HornCexSmtFilename, EC, sys::fs::F_Text);
      if (!EC) bmc.toSmtLib (file);
      else errs () << "Could not open: " << HornCexSmtFilename << "\n";
    }
    
    auto res = bmc.solve ();
    LOG ("cex",
         errs () << "BMC: " 
         << (res ? "sat" : (!res ? "unsat" : "unknown")) << "\n";);
    
    // -- DUMP unsat core if validation failed
    if (res) ;
    else
    {
      errs () << "Warning: failed to validate cex\n";
      errs () << "Computing unsat core\n";
      ExprVector core;
      bmc.unsatCore (core);
      errs () << "Final core: " << core.size () << "\n";
      errs () << "Failed to validate CEX. Core is: \n";
      for (Expr c : core) errs () << *c << "\n";
      
      Stats::sset("Result", "FAILED");
      return false;
    }
    
    // get bmc trace
    BmcTrace trace (bmc.getTrace ());

    if (!HornCexLLVM.empty()) {
      writeLLVMHarness(HornCexLLVM, M, F, trace);
    }

    LOG ("cex", trace.print (errs ()););

    dumpSvCompCex (trace);
    return false;
  }
  
  
  void HornCex::getAnalysisUsage (AnalysisUsage &AU) const
  {
    AU.setPreservesAll ();
    AU.addRequired<DataLayoutPass> ();
    AU.addRequired<CutPointGraph> ();
    AU.addRequired<HornifyModule> ();
    AU.addRequired<HornSolver> ();
    AU.addRequired<CanFail> ();
  }  
  
  /*** Helper methods to create SV-COMP style counterexamples */
  
  template <typename O>
  class SvCompCex
  {
    O &m_out;
    unsigned m_id;
    
    void key (std::string name, std::string type, std::string obj, std::string id)
    {
      m_out << "<key attr.name='" << name << "' attr.type='" << type << "'"
            << " for='" << obj << "' id='" << id << "'/>\n";
    }
    
  public:
    SvCompCex (O &out) : m_out (out), m_id(0) {}
    void header ()
    {
      m_out << "<graphml xmlns:xsi='http://www.w3.org/2001/XMLSchema-instance' "
            << "xmlns='http://graphml.graphdrawing.org/xmlns'>\n";
      key ("sourcecodeLanguage", "string", "graph", "sourcecodelang");
      key ("startline", "int", "edge", "originline");
      key ("originFileName", "string", "edge", "originfile");
      key ("isEntryNode", "boolean", "node", "entry");
      key ("isSinkNode", "boolean", "node", "sink");
      key ("isViolationNode", "boolean", "node", "violation");
      key ("enterFunction", "string", "edge", "enterFunction");
      key ("returnFromFunction", "string", "edge", "returnFrom");
      
      const std::string spec = "CHECK( init(main()), LTL(G ! call(__VERIFIER_error())) )";
      const std::string mem_model = "precise";
      const std::string arch = "32bit";

      m_out << "<graph edgedefault='directed'>\n"
            << "<data key='sourcecodelang'>C</data>\n"
            << "<data key='producer'>SeaHorn </data>\n"
            << "<data key='specification'>" << SvCompCexFileSpec << "</data>\n"
            << "<data key='memorymodel'>"   << SvCompCexFileMemModel << "</data>\n"
            << "<data key='architecture'>"  << SvCompCexFileArch << "</data>\n"
            << "<node id='0'> <data key='entry'>true</data> </node>\n";
    }

    void add_violation_node (){
      unsigned src = m_id++;
      m_out << "<node id='" << m_id << "'> <data key='violation'>true</data> </node>\n";      
      m_out << "<edge source='" << src << "' target='" << m_id << "'/>\n";
    }

    void edge (std::string file, int lineno, std::string scope)
    {
      unsigned src = m_id++;
      m_out << "<node id='" << m_id << "'/>\n";
      m_out << "<edge source='" << src << "' target='" << m_id << "'>\n";
      m_out << "  <data key='originline'>" << lineno << "</data>\n";
      m_out << "  <data key='originfile'>" << file << "</data>\n";

      if (boost::starts_with (scope, "enter: "))
        m_out << "  <data key='enterFunction'>" 
              << scope.substr (std::string ("enter: ").size ())
              << "</data>\n";
      else if (boost::starts_with (scope, "exit: "))
        m_out << "  <data key='returnFrom'>" 
              << scope.substr (std::string ("exit: ").size ())
              << "</data>\n";
      
      m_out << "</edge>\n";

    }
    
    void footer ()
    {
      m_out << "</graph></graphml>\n";
    }
  };

  template <typename O>
  static void debugLocToSvComp (const Instruction &inst, 
                                SvCompCex<O> &svcomp)
  {
    const DebugLoc &dloc = inst.getDebugLoc ();
    if (dloc.isUnknown ()) return;
    std::string file;

    DIScope Scope (dloc.getScope ());
    if (Scope) file = Scope.getFilename ();
    else file = "<unknown>";
    
    
    LOG ("cex",
         DISubprogram fnScope = getDISubprogram (dloc.getScope ());
         if (fnScope)
         {
           Function *fn = fnScope.getFunction ();
           StringRef dname = fnScope.getDisplayName ();
           if (const CallInst *ci = dyn_cast<const CallInst> (&inst))
           {
             Function *f = ci->getCalledFunction ();
             if (f && f->getName ().equals ("seahorn.fn.enter"))
               errs () << "entering: " << dname << "\n";
           }
           else
             errs () << "in: " << dname << "\n";
         });
      
    svcomp.edge (file, (int)dloc.getLine (), "");
  }
  
  
  static void dumpSvCompCex (BmcTrace &trace)
  {
    if (SvCompCexFile.empty ()) return;
    
    std::error_code ec;
    llvm::tool_output_file out (SvCompCexFile.c_str (), ec, llvm::sys::fs::F_Text);
    if (ec)
    {
      errs () << "ERROR: Cannot open CEX file: " << ec.message () << "\n";
      return;
    }
    
    SvCompCex<llvm::raw_ostream> svcomp (out.os ());
    svcomp.header ();
    for (unsigned i = 0; i < trace.size (); ++i)
    {
      const BasicBlock *bb = trace.bb (i);
      for (auto &I : *bb)
        debugLocToSvComp (I, svcomp);

      if (bb->getParent ()->getName ().equals ("main") && 
          isa<ReturnInst> (bb->getTerminator ())) 
        svcomp.add_violation_node ();
      
    }
    svcomp.footer ();
    out.keep ();
  }
  

}

