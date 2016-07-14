///
// seainspect -- Utilities for program inspection
///

#include "llvm/LinkAllPasses.h"
#include "llvm/PassManager.h"
#include "llvm/IR/LLVMContext.h"
#include "llvm/IR/Module.h"
#include "llvm/IRReader/IRReader.h"
#include "llvm/Support/FileSystem.h"
#include "llvm/Support/CommandLine.h"
#include "llvm/Support/Debug.h"
#include "llvm/Support/ManagedStatic.h"
#include "llvm/Support/PrettyStackTrace.h"
#include "llvm/Support/Signals.h"
#include "llvm/Support/SourceMgr.h"
#include "llvm/Support/ToolOutputFile.h"
#include "llvm/Support/raw_ostream.h"
#include "llvm/Transforms/IPO.h"
#include "llvm/Bitcode/ReaderWriter.h"
#include "llvm/IR/Verifier.h"

#include "seahorn/Passes.hh"
#include "seahorn/Analysis/DSA/BottomUp.hh"
#include "seahorn/Analysis/DSA/Local.hh"
#include "seahorn/Analysis/DSA/Global.hh"
#include "seahorn/Analysis/DSA/Info.hh"

static llvm::cl::opt<std::string>
InputFilename(llvm::cl::Positional, llvm::cl::desc("<input LLVM bitcode file>"),
              llvm::cl::Required, llvm::cl::value_desc("filename"));

static llvm::cl::opt<std::string>
DefaultDataLayout("default-data-layout",
                  llvm::cl::desc("data layout string to use if not specified by module"),
                  llvm::cl::init(""), llvm::cl::value_desc("layout-string"));


static llvm::cl::opt<bool>
Lint("lint",
     llvm::cl::desc("Statically lint-checks LLVM IR"),
     llvm::cl::init(false));

static llvm::cl::opt<bool>
Profiler("profiler",
         llvm::cl::desc("Profile a program for static analysis purposes"),
         llvm::cl::init(false));

static llvm::cl::opt<bool>
CfgDot("cfg-dot",
       llvm::cl::desc("Print CFG of function to dot format"),
       llvm::cl::init(false));

static llvm::cl::opt<bool>
CfgOnlyDot("cfg-only-dot",
           llvm::cl::desc("Print CFG of function (with no function bodies) to dot format"),
           llvm::cl::init(false));


static llvm::cl::opt<bool>
CfgViewer("cfg-viewer",
          llvm::cl::desc("View CFG of function"),
          llvm::cl::init(false));

static llvm::cl::opt<bool>
CfgOnlyViewer("cfg-only-viewer",
              llvm::cl::desc("View CFG of function (with no function bodies)"),
              llvm::cl::init(false));

static llvm::cl::opt<bool>
RunDsa("dsa",
       llvm::cl::desc("Print an abstraction of the heap"),
       llvm::cl::init(false));


int main(int argc, char **argv) {

  llvm::llvm_shutdown_obj shutdown;  // calls llvm_shutdown() on exit
  llvm::cl::ParseCommandLineOptions(argc, argv,
                                    "Utilities for program inspection");

  llvm::sys::PrintStackTraceOnErrorSignal();
  llvm::PrettyStackTraceProgram PSTP(argc, argv);
  llvm::EnableDebugBuffering = true;

  std::error_code error_code;
  llvm::SMDiagnostic err;
  llvm::LLVMContext &context = llvm::getGlobalContext();
  std::unique_ptr<llvm::Module> module;
  
  module = llvm::parseIRFile(InputFilename, err, context);
  if (module.get() == 0)
  {
    if (llvm::errs().has_colors()) llvm::errs().changeColor(llvm::raw_ostream::RED);
    llvm::errs() << "error: "
                 << "Bitcode was not properly read; " << err.getMessage() << "\n";
    if (llvm::errs().has_colors()) llvm::errs().resetColor();
    return 3;
  }
  
  llvm::PassManager pass_manager;

  llvm::PassRegistry &Registry = *llvm::PassRegistry::getPassRegistry();
  llvm::initializeAnalysis(Registry);
  /// call graph and other IPA passes
  llvm::initializeIPA (Registry);
  
  // add an appropriate DataLayout instance for the module
  const llvm::DataLayout *dl = module->getDataLayout ();
  if (!dl && !DefaultDataLayout.empty ()) {
    module->setDataLayout (DefaultDataLayout);
    dl = module->getDataLayout ();
  }
  if (dl) 
    pass_manager.add (new llvm::DataLayoutPass ());

  //pass_manager.add (llvm::createVerifierPass());

  if (Lint) {
    llvm::errs () << "Ran statically lint-like checks of LLVM IR\n";
    pass_manager.add (llvm::createLintPass ());
  }

  if (Profiler)
    pass_manager.add (seahorn::createProfilerPass ());

  if (CfgDot)  
    pass_manager.add (seahorn::createCFGPrinterPass ());

  if (CfgOnlyDot)
    pass_manager.add (seahorn::createCFGOnlyPrinterPass ());

  if (CfgViewer)  
    pass_manager.add (seahorn::createCFGViewerPass ());

  if (CfgOnlyViewer)
    pass_manager.add (seahorn::createCFGOnlyViewerPass ());

  // XXX: for now we just call the analysis pass.
  // Later we will have a pass that call this analysis pass and do
  // some pretty printer of the heap.
  if (RunDsa) {
    //pass_manager.add (new seahorn::dsa::BottomUp ());
    //pass_manager.add (new seahorn::dsa::Local ());
    //pass_manager.add (new seahorn::dsa::Global ());
    pass_manager.add (new seahorn::dsa::Info ());
  }

  pass_manager.run(*module.get());

  return 0;
}
