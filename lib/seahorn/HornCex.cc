#include "llvm/Analysis/TargetLibraryInfo.h"
#include "llvm/Bitcode/BitcodeWriter.h"
#include "llvm/IR/DataLayout.h"
#include "llvm/IR/DebugInfo.h"
#include "llvm/IR/DebugLoc.h"
#include "llvm/IR/Function.h"
#include "llvm/IR/GlobalValue.h"
#include "llvm/IR/IRBuilder.h"
#include "llvm/IR/IntrinsicInst.h"
#include "llvm/IR/ValueMap.h"
#include "llvm/IR/Verifier.h"
#include "llvm/Support/CommandLine.h"
#include "llvm/Support/FileSystem.h"
#include "llvm/Support/ToolOutputFile.h"

#include "seahorn/Analysis/SeaBuiltinsInfo.hh"
#include "seahorn/CexHarness.hh"
#include "seahorn/HornCex.hh"
#include "seahorn/MemSimulator.hh"

#include "seahorn/BvOpSem.hh"
#include "seahorn/UfoOpSem.hh"

#include "seahorn/Analysis/CanFail.hh"
#include "seahorn/Analysis/CutPointGraph.hh"
#include "seahorn/HornSolver.hh"
#include "seahorn/HornifyModule.hh"

#include "seahorn/Bmc.hh"
#include "seahorn/Support/CFG.hh"
#include "seahorn/Transforms/Utils/Local.hh"

#include "seahorn/Support/Stats.hh"
#include "seahorn/Support/SeaDebug.h"

#include "boost/algorithm/string/predicate.hpp"
#include "boost/container/flat_set.hpp"
#include "boost/container/map.hpp"
#include "boost/range.hpp"
#include "boost/range/adaptor/reversed.hpp"
#include "boost/range/algorithm/reverse.hpp"
#include "boost/range/algorithm/sort.hpp"

namespace seahorn {
std::string HornCexFile;
}

static llvm::cl::opt<std::string, true> XHornCexFile(
    "horn-cex",
    llvm::cl::desc(
        "Counterexample in SV-COMP (.xml) or LLVM bitcode (.bc or .ll) format"),
    llvm::cl::location(seahorn::HornCexFile),    
    llvm::cl::init(""),
    llvm::cl::value_desc("filename"));

static llvm::cl::opt<bool>
    UseBv("horn-cex-bv",
          llvm::cl::desc("Construct bit-precise counterexamples"),
          llvm::cl::init(false));

static llvm::cl::opt<bool>
    MemSim("horn-cex-bv-memsim",
           llvm::cl::desc("Run memory simulation on the counterexample"),
           llvm::cl::init(false));

static llvm::cl::opt<std::string> SvCompCexFileSpec(
    "horn-svcomp-cex-spec",
    llvm::cl::desc("Specification key in SV-COMP XML format"),
    llvm::cl::init("CHECK( init(main()), LTL(G ! call(__VERIFIER_error())) )"));

static llvm::cl::opt<std::string> SvCompCexFileMemModel(
    "horn-svcomp-cex-mem",
    llvm::cl::desc("Memory model key in SV-COMP XML format"),
    llvm::cl::init("simple"));

static llvm::cl::opt<std::string>
    SvCompCexFileArch("horn-svcomp-cex-arch",
                      llvm::cl::desc("Architecture key in SV-COMP XML format"),
                      llvm::cl::init("32bit"));

static llvm::cl::opt<std::string> HornCexSmtFilename(
    "horn-cex-smt", llvm::cl::desc("Counterexample validate SMT problem"),
    llvm::cl::init(""), llvm::cl::value_desc("filename"), llvm::cl::Hidden);

static llvm::cl::opt<std::string>
    BmcSliceOutputFile("horn-bmc-slice",
                       llvm::cl::desc("Output sliced bitcode by BmcTrace"),
                       llvm::cl::init(""), llvm::cl::value_desc("filename"));

static llvm::cl::opt<std::string> CpSliceOutputFile(
    "horn-cp-slice", llvm::cl::desc("Output sliced bitcode by cut point trace"),
    llvm::cl::init(""), llvm::cl::value_desc("filename"));

using namespace llvm;
namespace seahorn {

template <typename O> class SvCompCex;
static void dumpSvCompCex(BmcTrace &trace, std::string CexFile);
static void dumpLLVMBitcode(const Module &M, StringRef BcFile);

char HornCex::ID = 0;

bool HornCex::runOnModule(Module &M) {
  for (Function &F : M)
    if (F.getName().equals("main"))
      return runOnFunction(M, F);
  return false;
}

bool HornCex::runOnFunction(Module &M, Function &F) {
  HornSolver &hs = getAnalysis<HornSolver>();
  // -- only run if result is true, skip if it is false or unknown
  if (hs.getResult())
    ;
  else
    return false;

  // LOG ("cex",
  //      errs () << "Analyzed Function:\n"
  //      << F << "\n";);

  HornifyModule &hm = getAnalysis<HornifyModule>();
  const CutPointGraph &cpg = getAnalysis<CutPointGraph>(F);
  auto &SBI = getAnalysis<SeaBuiltinsInfoWrapperPass>().getSBI();

  Stats::resume("CexValidation");

  auto &fp = hs.getZFixedPoint();
  ExprVector rules;
  fp.getCexRules(rules);
  boost::reverse(rules);

  // extract a trace of basic blocks corresponding to the counterexample
  SmallVector<const BasicBlock *, 8> bbTrace;
  SmallVector<const CutPoint *, 8> cpTrace;

  // -- all counterexamples start at the entry block of the function
  cpTrace.push_back(&cpg.getCp(F.getEntryBlock()));

  for (Expr r : rules) {
    // filter away all rules not from main()
    Expr src, dst;

    {
      dst = isOpX<IMPL>(r) ? r->arg(1) : r;
      // -- skip rules whose destinations are not basic blocks
      if (!hm.isBbPredicate(dst))
        continue;
      const BasicBlock &bb = hm.predicateBb(dst);
      // -- skip basic blocks of non-main function
      if (bb.getParent() != &F)
        continue;
    }

    if (isOpX<IMPL>(r)) {
      dst = r->arg(1);
      r = r->arg(0);
      src = isOpX<AND>(r) ? r->arg(0) : r;
    } else
      dst = r;
    if (src && !bind::isFapp(src))
      src.reset(0);

    // -- if there is a src, then it was dst in previous iteration
    assert(bbTrace.empty() || bbTrace.back() == &hm.predicateBb(src));
    const BasicBlock *bb = &hm.predicateBb(dst);

    // XXX sometimes the cex includes the entry block, sometimes it does not
    // XXX normalize by removing it
    if (bb == &F.getEntryBlock())
      continue;

    bbTrace.push_back(bb);
    if (cpg.isCutPoint(*bb)) {
      const CutPoint &cp = cpg.getCp(*bb);
      cpTrace.push_back(&cp);
    }
  }

  LOG("cex", errs() << "TRACE BEGIN\n"; for (auto bb
                                             : bbTrace) {
    errs() << bb->getName();
    if (cpg.isCutPoint(*bb))
      errs() << " C";
    errs() << "\n";
  } errs() << "TRACE END\n";);

  // -- release trace resources
  bbTrace.clear();

  // -- abort if cpTrace is not well formed and it cannot be fixed.
  bool isCpTraceOK = true;
  if (cpTrace.empty()) {
    isCpTraceOK = false;
    errs() << "ERROR in cex generation: cex trace is empty.\n"
           << "The cex produced by the back-end solver is not enough to "
              "produce a bmc trace.\n"
           << "This typically happens if the program is too simple.\n";
  } else if (cpTrace.size() == 1 && F.size() > 1) {
    // cpTrace contains only the entry block but the function has more
    // than one block so cpTrace is missing some nodes
    if (F.size() == 2) {
      // The function consists only of an entry and an exit so we
      // fix the cpTrace and add the exit.
      const CutPoint *cp = cpTrace[0];
      const BasicBlock &bb = cp->bb();
      assert(&F.getEntryBlock() == &bb);
      auto kids = succs(bb);
      if (std::distance(kids.begin(), kids.end()) == 1) {
        const BasicBlock *kid = *(kids.begin());
        auto grandkids = succs(*kid);
        if (grandkids.begin() == grandkids.end()) {
          cpTrace.push_back(&cpg.getCp(*kid));
        }
      }
    } else {
      isCpTraceOK = false;
      errs() << "ERROR in cex generation: "
             << "cex trace contains only the entry block but it should contain "
                "some more blocks.\n"
             << "The cex produced by the back-end solver is not enough to "
                "produce a bmc trace.\n"
             << "This typically happens if the program is too simple.\n";
    }
  } else {
    const CutPoint *prev = nullptr;
    for (const CutPoint *cp : cpTrace) {
      if (prev) {
        const CpEdge *edg = cpg.getEdge(*prev, *cp);
        if (!edg) {
          // the trace is broken: we found a cp node for which there
          // is no successor.
          isCpTraceOK = false;
          errs() << "ERROR in cex generation: cex trace is incomplete.\n"
                 << "The cex produced by the back-end solver is not enough to "
                    "produce a bmc trace.\n"
                 << "This typically happens if the program is too simple.\n";
          break;
        }
      }
      prev = cp;
    }
  }

  if (!isCpTraceOK) {
    return false;
  }

  // -- create a BMC engine. Use fixed symbolic execution
  // -- semantics. Possibly different than the semantics used by the
  // -- HornSolver
  ExprFactory &efac = hm.getExprFactory();

  UfoOpSem semUfo(efac, *this, M.getDataLayout(), MEM);
  BvOpSem semBv(efac, *this, M.getDataLayout(), MEM);

  LegacyOperationalSemantics *sem =
      UseBv ? static_cast<LegacyOperationalSemantics *>(&semBv) : static_cast<LegacyOperationalSemantics *>(&semUfo);

  const TargetLibraryInfo &tli =
      getAnalysis<TargetLibraryInfoWrapperPass>().getTLI(F);

  BmcEngine bmc(*sem, hm.getZContext());

  // -- load the trace into the engine
  for (const CutPoint *cp : cpTrace)
    bmc.addCutPoint(*cp);

  // -- construct BMC instance
  bmc.encode();

  if (!HornCexSmtFilename.empty()) {
    std::error_code EC;
    raw_fd_ostream file(HornCexSmtFilename, EC, sys::fs::F_Text);
    if (!EC)
      bmc.toSmtLib(file);
    else
      errs() << "Could not open: " << HornCexSmtFilename << "\n";
  }

  auto res = bmc.solve();

  Stats::stop("CexValidation");

  LOG("cex", errs() << "BMC: " << (res ? "sat" : (!res ? "unsat" : "unknown"))
                    << "\n";);

  // -- DUMP unsat core if validation failed
  if (!res) {
    errs() << "Warning: the BMC engine failed to validate cex\n";
    errs() << "Computing unsat core\n";
    ExprVector core;
    bmc.unsatCore(core);
    errs() << "Final core: " << core.size() << "\n";
    errs() << "Core is: \n";
    for (Expr c : core)
      errs() << *c << "\n";
    Stats::sset("Result", "FAILED");
    return false;
  }

  LOG("cex", errs() << "Validated CEX by BMC engine.\n";);

  // get bmc trace
  BmcTrace trace(bmc.getTrace());
  LOG("cex", trace.print(errs()));
  std::unique_ptr<MemSimulator> memSim = nullptr;

  if (UseBv) {
    const DataLayout &dl = M.getDataLayout();
    const TargetLibraryInfo &tli =
        getAnalysis<TargetLibraryInfoWrapperPass>().getTLI(F);
    if (MemSim) {
      memSim = std::unique_ptr<MemSimulator>(new MemSimulator(trace, dl, tli));
      bool simRes = memSim->simulate();
      if (!simRes) {
        // errs () << "Warning: memory simulation failed.\n";
        memSim.reset();
      } else {
        // errs () << "Warning: memory simulation succeed!\n";
      }
    } else {
      // errs () << "Warning: memory simulation is not enabled.\n";
    }
  }

  StringRef HornCexFileRef(HornCexFile);
  if (HornCexFileRef.endswith(".ll") || HornCexFileRef.endswith(".bc")) {
    const DataLayout &dl = M.getDataLayout();
    std::unique_ptr<BmcTraceWrapper> traceW(new BmcTraceWrapper(trace));
    if (memSim) {
      traceW.reset(new BmcTraceMemSim(*memSim));
    }
    dumpLLVMCex(*traceW, HornCexFileRef, dl, tli, F.getContext());
  } else if (HornCexFileRef.endswith(".xml")) {
    dumpSvCompCex(trace, HornCexFileRef);
  } else if (!HornCexFileRef.empty()) {
    errs() << "Unrecognized counter-example file suffix in " << HornCexFileRef
           << ". Expected .xml, .ll, or .bc.\n";
  }

  if (!BmcSliceOutputFile.empty()) {
    llvm::DenseSet<const llvm::BasicBlock *> region;
    for (int i = 0; i < trace.size(); i++)
      region.insert(trace.bb(i));
    reduceToRegion(F, region, SBI);
    dumpLLVMBitcode(M, BmcSliceOutputFile.c_str());
    return true;
  }

  if (!CpSliceOutputFile.empty()) {
    DenseSet<const BasicBlock *> region;
    for (int i = 0; i < cpTrace.size(); i++) {
      const CutPoint *cp = cpTrace[i];
      region.insert(&cp->bb());
      for (CutPoint::const_iterator it = cp->succ_begin(); it != cp->succ_end();
           it++) {
        const CpEdge *const edge = *it;
        if (&edge->target() == cpTrace[i + 1]) {
          for (CpEdge::const_iterator bb = edge->begin(); bb != edge->end();
               bb++) {
            region.insert(&*bb);
          }
        }
      }
    }
    reduceToRegion(F, region, SBI);
    dumpLLVMBitcode(M, CpSliceOutputFile.c_str());
    return true;
  }

  return false;
}

void HornCex::getAnalysisUsage(AnalysisUsage &AU) const {
  AU.setPreservesAll();
  AU.addRequired<TargetLibraryInfoWrapperPass>();
  AU.addRequired<SeaBuiltinsInfoWrapperPass>();
  AU.addRequired<CutPointGraph>();
  AU.addRequired<HornifyModule>();
  AU.addRequired<HornSolver>();
  AU.addRequired<CanFail>();
}

/*** Helper methods to create SV-COMP style counterexamples */

template <typename O> class SvCompCex {
  O &m_out;
  unsigned m_id;

  void key(std::string name, std::string type, std::string obj,
           std::string id) {
    m_out << "<key attr.name='" << name << "' attr.type='" << type << "'"
          << " for='" << obj << "' id='" << id << "'/>\n";
  }

public:
  SvCompCex(O &out) : m_out(out), m_id(0) {}
  void header() {
    m_out << "<graphml xmlns:xsi='http://www.w3.org/2001/XMLSchema-instance' "
          << "xmlns='http://graphml.graphdrawing.org/xmlns'>\n";
    key("sourcecodeLanguage", "string", "graph", "sourcecodelang");
    key("startline", "int", "edge", "originline");
    key("originFileName", "string", "edge", "originfile");
    key("isEntryNode", "boolean", "node", "entry");
    key("isSinkNode", "boolean", "node", "sink");
    key("isViolationNode", "boolean", "node", "violation");
    key("enterFunction", "string", "edge", "enterFunction");
    key("returnFromFunction", "string", "edge", "returnFrom");

    const std::string spec =
        "CHECK( init(main()), LTL(G ! call(__VERIFIER_error())) )";
    const std::string mem_model = "precise";
    const std::string arch = "32bit";

    m_out << "<graph edgedefault='directed'>\n"
          << "<data key='sourcecodelang'>C</data>\n"
          << "<data key='producer'>SeaHorn </data>\n"
          << "<data key='specification'>" << SvCompCexFileSpec << "</data>\n"
          << "<data key='memorymodel'>" << SvCompCexFileMemModel << "</data>\n"
          << "<data key='architecture'>" << SvCompCexFileArch << "</data>\n"
          << "<node id='0'> <data key='entry'>true</data> </node>\n";
  }

  void add_violation_node() {
    unsigned src = m_id++;
    m_out << "<node id='" << m_id
          << "'> <data key='violation'>true</data> </node>\n";
    m_out << "<edge source='" << src << "' target='" << m_id << "'/>\n";
  }

  void edge(std::string file, int lineno, std::string scope) {
    unsigned src = m_id++;
    m_out << "<node id='" << m_id << "'/>\n";
    m_out << "<edge source='" << src << "' target='" << m_id << "'>\n";
    m_out << "  <data key='originline'>" << lineno << "</data>\n";
    m_out << "  <data key='originfile'>" << file << "</data>\n";

    if (boost::starts_with(scope, "enter: "))
      m_out << "  <data key='enterFunction'>"
            << scope.substr(std::string("enter: ").size()) << "</data>\n";
    else if (boost::starts_with(scope, "exit: "))
      m_out << "  <data key='returnFrom'>"
            << scope.substr(std::string("exit: ").size()) << "</data>\n";

    m_out << "</edge>\n";
  }

  void footer() { m_out << "</graph></graphml>\n"; }
};

template <typename O>
static void debugLocToSvComp(const Instruction &inst, SvCompCex<O> &svcomp) {
  const DebugLoc &dloc = inst.getDebugLoc();
  if (!(dloc.get()))
    return;
  std::string file;

  // DIScope Scope (dloc.getScope ());
  // if (Scope) file = Scope.getFilename ();
  // else file = "<unknown>";
  // XXX: porting to llvm 3.8
  file = dloc.get()->getFilename();

  // TODO: port to llvm 3.8
  //
  // LOG ("cex",
  //      DISubprogram fnScope = getDISubprogram (*(dloc.getScope ()));
  //      if (fnScope)
  //      {
  //        Function *fn = fnScope.getFunction ();
  //        StringRef dname = fnScope.getDisplayName ();
  //        if (const CallInst *ci = dyn_cast<const CallInst> (&inst))
  //        {
  //          Function *f = ci->getCalledFunction ();
  //          if (f && f->getName ().equals ("seahorn.fn.enter"))
  //            errs () << "entering: " << dname << "\n";
  //        }
  //        else
  //          errs () << "in: " << dname << "\n";
  //      });

  svcomp.edge(file, (int)dloc.getLine(), "");
}

static void dumpSvCompCex(BmcTrace &trace, std::string CexFile) {
  std::error_code ec;
  llvm::ToolOutputFile out(CexFile.c_str(), ec, llvm::sys::fs::F_Text);
  if (ec) {
    errs() << "ERROR: Cannot open CEX file: " << ec.message() << "\n";
    return;
  }

  SvCompCex<llvm::raw_ostream> svcomp(out.os());
  svcomp.header();
  for (unsigned i = 0; i < trace.size(); ++i) {
    const BasicBlock *bb = trace.bb(i);
    for (auto &I : *bb)
      debugLocToSvComp(I, svcomp);

    if (bb->getParent()->getName().equals("main") &&
        isa<ReturnInst>(bb->getTerminator()))
      svcomp.add_violation_node();
  }
  svcomp.footer();
  out.keep();
}

static void dumpLLVMBitcode(const Module &M, StringRef BcFile) {
  std::error_code error_code;
  ToolOutputFile sliceOutput(BcFile, error_code, sys::fs::F_None);
  assert(!error_code);
  verifyModule(M, &errs());
  if (BcFile.endswith(".ll"))
    sliceOutput.os() << M;
  else
    WriteBitcodeToFile(M, sliceOutput.os());
  sliceOutput.os().close();
  sliceOutput.keep();
}

} // namespace seahorn
