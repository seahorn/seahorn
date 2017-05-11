// Derived from https://github.com/smackers/smack/blob/master/tools/smack/smack.cpp
//
// Copyright (c) 2013 Pantazis Deligiannis (p.deligiannis@imperial.ac.uk)
// This file is distributed under the MIT License. See LICENSE for details.
//

#include "llvm/LinkAllPasses.h"
#include "llvm/PassManager.h"
#include "llvm/IR/LLVMContext.h"
#include "llvm/IR/Module.h"
#include "llvm/IRReader/IRReader.h"
#include "llvm/Support/CommandLine.h"
#include "llvm/Support/raw_ostream.h"
#include "llvm/Support/Debug.h"
#include "llvm/Support/ManagedStatic.h"
#include "llvm/Support/PrettyStackTrace.h"
#include "llvm/Support/Signals.h"
#include "llvm/Support/SourceMgr.h"
#include "llvm/Support/ToolOutputFile.h"
#include "llvm/Support/raw_ostream.h"
#include "llvm/Support/FileSystem.h"
#include "llvm/Transforms/IPO.h"

#include "seahorn/config.h"
#include "seahorn/Passes.hh"
#include "seahorn/HornWrite.hh"
#include "seahorn/HornifyModule.hh"
#include "seahorn/HornSolver.hh"
#include "seahorn/Houdini.hh"
#include "seahorn/ICE.hh"
#include "seahorn/PredicateAbstraction.hh"
#include "seahorn/HornCex.hh"
#include "seahorn/Transforms/Scalar/PromoteVerifierCalls.hh"
#include "seahorn/Transforms/Scalar/LowerGvInitializers.hh"
#include "seahorn/Transforms/Scalar/LowerCstExpr.hh"
#include "seahorn/Transforms/Utils/RemoveUnreachableBlocksPass.hh"

#ifdef HAVE_CRAB_LLVM
#include "crab_llvm/CrabLlvm.hh"
#include "crab_llvm/Transforms/InsertInvariants.hh"
#endif

#include "ufo/Smt/EZ3.hh"
#include "ufo/Passes/NameValues.hpp"
#include "ufo/Stats.hh"

void print_seahorn_version()
{
  llvm::outs () << "SeaHorn (http://seahorn.github.io/):\n"
                << "  SeaHorn version " << SEAHORN_VERSION_INFO << "\n";
}

/// XXX HACK to force compiler to link this in
namespace seahorn
{
  struct ZTraceLogOpt
  {
    void operator= (const std::string &tag) const
    {Z3_enable_trace (tag.c_str ());}
  };
  ZTraceLogOpt ztrace;

  struct ZVerboseOpt
  {
    void operator= (const int v) const
    {z3::set_param ("verbose", v);}
  };
  ZVerboseOpt zverbose;
}

static llvm::cl::opt<seahorn::ZTraceLogOpt, true, llvm::cl::parser<std::string> >
TraceOption ("ztrace",
             llvm::cl::desc ("Enable z3 trace level"),
             llvm::cl::location (seahorn::ztrace),
             llvm::cl::value_desc ("string"),
             llvm::cl::ValueRequired, llvm::cl::ZeroOrMore,
             llvm::cl::Hidden);

static llvm::cl::opt<seahorn::ZVerboseOpt, true, llvm::cl::parser<int> >
VerboseOption ("zverbose",
               llvm::cl::desc ("Z3 verbosity level"),
               llvm::cl::location (seahorn::zverbose),
               llvm::cl::value_desc ("int"),
               llvm::cl::ValueRequired, llvm::cl::Hidden);


static llvm::cl::opt<std::string>
InputFilename(llvm::cl::Positional, llvm::cl::desc("<input LLVM bitcode file>"),
              llvm::cl::Required, llvm::cl::value_desc("filename"));

static llvm::cl::opt<std::string>
OutputFilename("o", llvm::cl::desc("Override output filename"),
               llvm::cl::init(""), llvm::cl::value_desc("filename"));


static llvm::cl::opt<std::string>
AsmOutputFilename("oll", llvm::cl::desc("Output analyzed bitcode"),
               llvm::cl::init(""), llvm::cl::value_desc("filename"));

static llvm::cl::opt<std::string>
DefaultDataLayout("default-data-layout",
                  llvm::cl::desc("data layout string to use if not specified by module"),
                  llvm::cl::init(""), llvm::cl::value_desc("layout-string"));

static llvm::cl::opt<bool>
InlineAll ("horn-inline-all", llvm::cl::desc ("Inline all functions"),
           llvm::cl::init (false));

static llvm::cl::opt<bool>
Solve ("horn-solve", llvm::cl::desc ("Run Horn solver"), llvm::cl::init (false));

static llvm::cl::opt<bool>
Crab ("horn-crab", llvm::cl::desc ("Use Crab invariants"), llvm::cl::init (false));

static llvm::cl::opt<bool>
PrintStats ("horn-stats",
            llvm::cl::desc ("Print statistics"), llvm::cl::init(false));

static llvm::cl::opt<bool>
Cex ("horn-cex-pass", llvm::cl::desc ("Produce detailed counterexample"),
     llvm::cl::init (false));

static llvm::cl::opt<bool>
KeepShadows ("keep-shadows", llvm::cl::desc ("Do not strip shadow.mem functions"),
             llvm::cl::init (false), llvm::cl::Hidden);

static llvm::cl::opt<bool>
Bmc ("horn-bmc",
     llvm::cl::desc ("Use BMC engine. Currently restricted to intra-procedural analysis"),
     llvm::cl::init (false));

static llvm::cl::opt<bool>
SeaHornDsa ("horn-sea-dsa",
            llvm::cl::desc ("Use Seahorn Dsa analysis"),
            llvm::cl::init (false));

static llvm::cl::opt<bool>
HoudiniInv ("horn-houdini",
         llvm::cl::desc ("Use Houdini algorithm to generate inductive invariants"),
         llvm::cl::init (false));

static llvm::cl::opt<bool>
PredAbs ("horn-pred-abs",
        llvm::cl::desc ("Use Predicate Abstraction to generate inductive invariants"),
        llvm::cl::init (false));

static llvm::cl::opt<bool>
ICEInv ("horn-ice",
        llvm::cl::desc ("Use ICE to generate inductive invariants"),
        llvm::cl::init (false));

// removes extension from filename if there is one
std::string getFileName(const std::string &str) {
  std::string filename = str;
  size_t lastdot = str.find_last_of(".");
  if (lastdot != std::string::npos)
    filename = str.substr(0, lastdot);
  return filename;
}

int main(int argc, char **argv) {
  ufo::ScopedStats _st ("seahorn_total");

  llvm::llvm_shutdown_obj shutdown;  // calls llvm_shutdown() on exit
  llvm::cl::AddExtraVersionPrinter (print_seahorn_version);
  llvm::cl::ParseCommandLineOptions(argc, argv,
                                    "SeaHorn -- LLVM bitcode to Horn/SMT2 transformation\n");

  llvm::sys::PrintStackTraceOnErrorSignal();
  llvm::PrettyStackTraceProgram PSTP(argc, argv);
  llvm::EnableDebugBuffering = true;

  std::error_code error_code;
  llvm::SMDiagnostic err;
  llvm::LLVMContext &context = llvm::getGlobalContext();
  std::unique_ptr<llvm::Module> module;
  std::unique_ptr<llvm::tool_output_file> output;
  std::unique_ptr<llvm::tool_output_file> asmOutput;


  module = llvm::parseIRFile(InputFilename, err, context);
  if (module.get() == 0)
  {
    if (llvm::errs().has_colors()) llvm::errs().changeColor(llvm::raw_ostream::RED);
    llvm::errs() << "error: "
                 << "Bitcode was not properly read; " << err.getMessage() << "\n";
    if (llvm::errs().has_colors()) llvm::errs().resetColor();
    return 3;
  }
  if (!AsmOutputFilename.empty ())
    asmOutput =
      llvm::make_unique<llvm::tool_output_file>(AsmOutputFilename.c_str(), error_code,
                                                llvm::sys::fs::F_Text);
  if (error_code) {
    if (llvm::errs().has_colors())
      llvm::errs().changeColor(llvm::raw_ostream::RED);
    llvm::errs() << "error: Could not open " << AsmOutputFilename << ": "
                 << error_code.message () << "\n";
    if (llvm::errs().has_colors()) llvm::errs().resetColor();
    return 3;
  }

  if (!OutputFilename.empty ())
    output = llvm::make_unique<llvm::tool_output_file>
      (OutputFilename.c_str(), error_code, llvm::sys::fs::F_None);

  if (error_code) {
    if (llvm::errs().has_colors()) llvm::errs().changeColor(llvm::raw_ostream::RED);
    llvm::errs() << "error: Could not open " << OutputFilename << ": "
                 << error_code.message () << "\n";
    if (llvm::errs().has_colors()) llvm::errs().resetColor();
    return 3;
  }


  ///////////////////////////////
  // initialise and run passes //
  ///////////////////////////////

  llvm::PassManager pass_manager;
  llvm::PassRegistry &Registry = *llvm::PassRegistry::getPassRegistry();
  llvm::initializeAnalysis(Registry);

  /// call graph and other IPA passes
  llvm::initializeIPA (Registry);

  // add an appropriate DataLayout instance for the module
  const llvm::DataLayout *dl = module->getDataLayout ();
  if (!dl && !DefaultDataLayout.empty ())
  {
    module->setDataLayout (DefaultDataLayout);
    dl = module->getDataLayout ();
  }

  if (dl) pass_manager.add (new llvm::DataLayoutPass ());

  // turn all functions internal so that we can inline them if requested
  pass_manager.add (llvm::createInternalizePass (llvm::ArrayRef<const char*>("main")));
  pass_manager.add (llvm::createGlobalDCEPass ()); // kill unused internal global

  if (InlineAll)
  {
    pass_manager.add (seahorn::createMarkInternalInlinePass ());
    pass_manager.add (llvm::createAlwaysInlinerPass ());
    pass_manager.add (llvm::createGlobalDCEPass ()); // kill unused internal global
  }
  pass_manager.add (new seahorn::RemoveUnreachableBlocksPass ());

  pass_manager.add(llvm::createPromoteMemoryToRegisterPass());
  pass_manager.add (new seahorn::PromoteVerifierCalls ());
  pass_manager.add(llvm::createDeadInstEliminationPass());
  pass_manager.add(llvm::createLowerSwitchPass());
  // lowers constant expressions to instructions
  pass_manager.add(new seahorn::LowerCstExprPass());
  pass_manager.add(llvm::createDeadCodeEliminationPass());

  pass_manager.add(llvm::createUnifyFunctionExitNodesPass ());

  // -- it invalidates DSA passes so it should be run before
  // -- ShadowMemDsa
  pass_manager.add (llvm::createGlobalDCEPass ()); // kill unused internal global
  if (SeaHornDsa)
    pass_manager.add (seahorn::createShadowMemSeaDsaPass ());
  else
    pass_manager.add (seahorn::createShadowMemDsaPass ());
  // lowers shadow.mem variables created by ShadowMemDsa pass
  pass_manager.add (seahorn::createPromoteMemoryToRegisterPass ());

  pass_manager.add (new seahorn::RemoveUnreachableBlocksPass ());
  pass_manager.add (seahorn::createStripLifetimePass ());
  pass_manager.add (seahorn::createDeadNondetElimPass ());

#ifdef HAVE_CRAB_LLVM
  if (Crab)
  {
    /// -- insert invariants in the bitecode
    pass_manager.add (new crab_llvm::InsertInvariants ());
    /// -- simplify invariants added in the bitecode
    // pass_manager.add (seahorn::createInstCombine ());
  }
#endif

  // --- verify if an undefined value can be read
  pass_manager.add (seahorn::createCanReadUndefPass ());

  if (!Bmc)
    pass_manager.add (new seahorn::HornifyModule ());
  if (!AsmOutputFilename.empty ())
  {
    if (!KeepShadows)
    {
      pass_manager.add (new ufo::NameValues ());
      // -- XXX might destroy names using by HornSolver later on.
      // -- XXX it is probably dangerous to strip shadows and solve at the same time
      pass_manager.add (seahorn::createStripShadowMemPass ());
    }
    pass_manager.add (createPrintModulePass (asmOutput->os ()));
  }

  if (Bmc)
  {
    llvm::raw_ostream *out = nullptr;
    if (!OutputFilename.empty ()) out = &output->os ();
    pass_manager.add (seahorn::createBmcPass (out, Solve));
  }
  else
  {
    if (!OutputFilename.empty ()) pass_manager.add (new seahorn::HornWrite (output->os ()));
    if (Crab) pass_manager.add (seahorn::createLoadCrabPass ());
    if (HoudiniInv) pass_manager.add (new seahorn::HoudiniPass ());
    if (ICEInv) pass_manager.add (new seahorn::ICEPass ());
    if (PredAbs) pass_manager.add(new seahorn::PredicateAbstraction());
    if (Solve)
    { 	  pass_manager.add (new seahorn::HornSolver ());
          if (Cex) pass_manager.add (new seahorn::HornCex ());
    }
  }

  pass_manager.run(*module.get());

  if (!AsmOutputFilename.empty ()) asmOutput->keep ();
  if (!OutputFilename.empty ()) output->keep();
  if (PrintStats) ufo::Stats::PrintBrunch (llvm::outs ());
  return 0;
}
