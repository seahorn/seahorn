///
// seainspect -- Utilities for program inspection
///

#include "llvm/Bitcode/BitcodeWriter.h"
#include "llvm/IR/LLVMContext.h"
#include "llvm/IR/LegacyPassManager.h"
#include "llvm/IR/Module.h"
#include "llvm/IR/Verifier.h"
#include "llvm/IRReader/IRReader.h"
#include "llvm/InitializePasses.h"
#include "llvm/LinkAllPasses.h"
#include "llvm/Support/CommandLine.h"
#include "llvm/Support/Debug.h"
#include "llvm/Support/FileSystem.h"
#include "llvm/Support/ManagedStatic.h"
#include "llvm/Support/PrettyStackTrace.h"
#include "llvm/Support/Signals.h"
#include "llvm/Support/SourceMgr.h"
#include "llvm/Support/ToolOutputFile.h"
#include "llvm/Support/raw_ostream.h"
#include "llvm/Transforms/IPO.h"

#include "seadsa/DsaAnalysis.hh"
#include "seadsa/InitializePasses.hh"

#include "seahorn/Passes.hh"

static llvm::cl::opt<std::string>
    InputFilename(llvm::cl::Positional,
                  llvm::cl::desc("<input LLVM bitcode file>"),
                  llvm::cl::Required, llvm::cl::value_desc("filename"));

static llvm::cl::opt<std::string>
    AsmOutputFilename("oll", llvm::cl::desc("Output analyzed bitcode"),
                      llvm::cl::init(""), llvm::cl::value_desc("filename"));

static llvm::cl::opt<std::string> DefaultDataLayout(
    "data-layout",
    llvm::cl::desc("data layout string to use if not specified by module"),
    llvm::cl::init(""), llvm::cl::value_desc("layout-string"));

static llvm::cl::opt<bool>
    Profiler("profiler",
             llvm::cl::desc("Profile a program for static analysis purposes"),
             llvm::cl::init(false));

static llvm::cl::opt<bool>
    CfgDot("cfg-dot", llvm::cl::desc("Print CFG of function to dot format"),
           llvm::cl::init(false));

static llvm::cl::opt<bool> CfgOnlyDot(
    "cfg-only-dot",
    llvm::cl::desc(
        "Print CFG of function (without instructions) to dot format"),
    llvm::cl::init(false));

static llvm::cl::opt<bool> CfgViewer("cfg-viewer",
                                     llvm::cl::desc("View CFG of function"),
                                     llvm::cl::Hidden, llvm::cl::init(false));

static llvm::cl::opt<bool>
    CfgOnlyViewer("cfg-only-viewer",
                  llvm::cl::desc("View CFG of function (without instructions)"),
                  llvm::cl::Hidden, llvm::cl::init(false));

static llvm::cl::opt<bool> MemDot(
    "mem-dot",
    llvm::cl::desc("Print SeaDsa memory graph of a function to dot format"),
    llvm::cl::init(false));

static llvm::cl::opt<bool> MemViewer(
    "mem-viewer",
    llvm::cl::desc("View SeaDsa memory graph of a function to dot format"),
    llvm::cl::Hidden, llvm::cl::init(false));

static llvm::cl::opt<bool> PrintMemStats(
    "mem-stats",
    llvm::cl::desc("Print statistics about all SeaDsa memory graphs"),
    llvm::cl::init(false));

static llvm::cl::opt<bool>
    SMC("mem-smc-stats",
        llvm::cl::desc(
            "Print statistics collected by our SMC (Simple Memory Checker)"),
        llvm::cl::init(false));

static llvm::cl::opt<bool> CallGraphDot(
    "mem-callgraph-dot",
    llvm::cl::desc("Print complete SeaDsa call graph to dot format"),
    llvm::cl::init(false));

static llvm::cl::opt<bool> PrintCallGraphStats(
    "mem-callgraph-stats",
    llvm::cl::desc("Print statistics about the complete SeaDsa call graph"),
    llvm::cl::init(false));

static llvm::cl::opt<bool>
    RunGSA("run-gsa", llvm::cl::desc("Run Gated SSA (GSA) construction"),
           llvm::cl::init(false));

static llvm::cl::opt<bool>
    RunCDA("run-cda", llvm::cl::desc("Run Control Dependence Analysis (CDA)"),
           llvm::cl::init(false));

static llvm::cl::opt<bool> RunCHA(
    "cha",
    llvm::cl::desc("Print Class Hierarchy Analysis (CHA) (very experimental)"),
    llvm::cl::init(false));

int main(int argc, char **argv) {

  llvm::llvm_shutdown_obj shutdown; // calls llvm_shutdown() on exit
  llvm::cl::ParseCommandLineOptions(argc, argv,
                                    "Utilities for program inspection");

  llvm::sys::PrintStackTraceOnErrorSignal(argv[0]);
  llvm::PrettyStackTraceProgram PSTP(argc, argv);
  llvm::EnableDebugBuffering = true;

  std::error_code error_code;
  llvm::SMDiagnostic err;
  static llvm::LLVMContext context;
  std::unique_ptr<llvm::Module> module;
  std::unique_ptr<llvm::ToolOutputFile> asmOutput;

  module = llvm::parseIRFile(InputFilename, err, context);
  if (module.get() == 0) {
    if (llvm::errs().has_colors())
      llvm::errs().changeColor(llvm::raw_ostream::RED);
    llvm::errs() << "error: "
                 << "Bitcode was not properly read; " << err.getMessage()
                 << "\n";
    if (llvm::errs().has_colors())
      llvm::errs().resetColor();
    return 3;
  }

  if (!AsmOutputFilename.empty())
    asmOutput = std::make_unique<llvm::ToolOutputFile>(
        AsmOutputFilename.c_str(), error_code, llvm::sys::fs::F_Text);
  if (error_code) {
    if (llvm::errs().has_colors())
      llvm::errs().changeColor(llvm::raw_ostream::RED);
    llvm::errs() << "error: Could not open " << AsmOutputFilename << ": "
                 << error_code.message() << "\n";
    if (llvm::errs().has_colors())
      llvm::errs().resetColor();
    return 3;
  }

  ///////////////////////////////
  // initialise and run passes //
  ///////////////////////////////

  llvm::legacy::PassManager pass_manager;
  llvm::PassRegistry &Registry = *llvm::PassRegistry::getPassRegistry();
  llvm::initializeAnalysis(Registry);

  /// call graph and other IPA passes
  // llvm::initializeIPA (Registry);
  // XXX: porting to 3.8
  llvm::initializeCallGraphWrapperPassPass(Registry);
  // XXX: commented while porting to 5.0
  // llvm::initializeCallGraphPrinterPass(Registry);
  llvm::initializeCallGraphViewerPass(Registry);
  // XXX: not sure if needed anymore
  llvm::initializeGlobalsAAWrapperPassPass(Registry);

  // Needed for error message: Pass 'SeaHorn Dsa graph printer' is not
  // initialized.
  llvm::initializeDsaAnalysisPass(Registry);

  // add an appropriate DataLayout instance for the module
  const llvm::DataLayout *dl = &module->getDataLayout();
  if (!dl && !DefaultDataLayout.empty()) {
    module->setDataLayout(DefaultDataLayout);
    dl = &module->getDataLayout();
  }

  assert(dl && "Could not find Data Layout for the module");

  // pass_manager.add (llvm::createVerifierPass());

  // XXX: run Dsa passes before CFG passes
  if (MemDot)
    pass_manager.add(seadsa::createDsaPrinterPass());

  if (CallGraphDot)
    pass_manager.add(seadsa::createDsaCallGraphPrinterPass());

  if (PrintCallGraphStats)
    pass_manager.add(seadsa::createDsaPrintCallGraphStatsPass());

  if (MemViewer)
    pass_manager.add(seadsa::createDsaViewerPass());

  if (PrintMemStats)
    pass_manager.add(seadsa::createDsaPrintStatsPass());

  if (SMC)
    pass_manager.add(seahorn::createSimpleMemoryCheckPass());

  if (Profiler)
    pass_manager.add(seahorn::createProfilerPass());

  if (CfgDot)
    pass_manager.add(seahorn::createCFGPrinterPass());

  if (CfgOnlyDot)
    pass_manager.add(seahorn::createCFGOnlyPrinterPass());

  if (CfgViewer)
    pass_manager.add(seahorn::createCFGViewerPass());

  if (CfgOnlyViewer)
    pass_manager.add(seahorn::createCFGOnlyViewerPass());

  if (RunGSA)
    pass_manager.add(seahorn::createGateAnalysisPass());

  if (RunCDA)
    pass_manager.add(seahorn::createControlDependenceAnalysisPass());

  if (RunCHA)
    pass_manager.add(seahorn::createCHAPass());

  if (!AsmOutputFilename.empty())
    pass_manager.add(createPrintModulePass(asmOutput->os()));

  pass_manager.run(*module.get());

  if (!AsmOutputFilename.empty())
    asmOutput->keep();

  return 0;
}
