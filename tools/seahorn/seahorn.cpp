// Derived from
// https://github.com/smackers/smack/blob/master/tools/smack/smack.cpp
//
// Copyright (c) 2013 Pantazis Deligiannis (p.deligiannis@imperial.ac.uk)
// This file is distributed under the MIT License. See LICENSE for details.
//

#include "llvm_seahorn/InitializePasses.h"
#include "llvm_seahorn/Transforms/IPO.h"
#include "llvm/IR/LLVMContext.h"
#include "llvm/IR/LegacyPassManager.h"
#include "llvm/IR/Module.h"
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

#include "seahorn/HornCex.hh"
#include "seahorn/HornSolver.hh"
#include "seahorn/HornWrite.hh"
#include "seahorn/HornifyModule.hh"
#include "seahorn/Houdini.hh"
#include "seahorn/InitializePasses.hh"
#include "seahorn/Passes.hh"
#include "seahorn/PredicateAbstraction.hh"
#include "seahorn/Support/SeaLog.hh"
#include "seahorn/Transforms/Scalar/LowerCstExpr.hh"
#include "seahorn/Transforms/Scalar/LowerGvInitializers.hh"
#include "seahorn/Transforms/Scalar/PromoteVerifierCalls.hh"
#include "seahorn/Transforms/Utils/RemoveUnreachableBlocksPass.hh"
#include "seahorn/config.h"

#ifdef HAVE_CLAM
#include "clam/Clam.hh"
#endif

#include "seadsa/DsaAnalysis.hh"
#include "seadsa/InitializePasses.hh"
#include "seadsa/support/RemovePtrToInt.hh"

#include "seahorn/Expr/Smt/EZ3.hh"
#include "seahorn/Support/Stats.hh"
#include "seahorn/Transforms/Utils/NameValues.hh"

#include "seahorn/Support/GitSHA1.h"
void print_seahorn_version(llvm::raw_ostream &OS) {
  OS << "SeaHorn (http://seahorn.github.io/):\n"
     << "  SeaHorn version " << SEAHORN_VERSION_INFO << "-" << g_GIT_SHA1
     << "\n";
}

/// XXX HACK to force compiler to link this in
namespace seahorn {
struct ZTraceLogOpt {
  void operator=(const std::string &tag) const { Z3_enable_trace(tag.c_str()); }
};
ZTraceLogOpt ztrace;

struct ZVerboseOpt {
  void operator=(const int v) const { z3::set_param("verbose", v); }
};
ZVerboseOpt zverbose;

struct CVerboseOpt {
#ifdef HAVE_CLAM
  void operator=(unsigned level) const { crab::CrabEnableVerbosity(level); }
#else
  void operator=(unsigned level) const {}
#endif
};

CVerboseOpt cverbose;
} // namespace seahorn

static llvm::cl::opt<seahorn::ZTraceLogOpt, true, llvm::cl::parser<std::string>>
    TraceOption("ztrace", llvm::cl::desc("Enable z3 trace level"),
                llvm::cl::location(seahorn::ztrace),
                llvm::cl::value_desc("string"), llvm::cl::ValueRequired,
                llvm::cl::ZeroOrMore, llvm::cl::Hidden);

static llvm::cl::opt<seahorn::ZVerboseOpt, true, llvm::cl::parser<int>>
    VerboseOption("zverbose", llvm::cl::desc("Z3 verbosity level"),
                  llvm::cl::location(seahorn::zverbose),
                  llvm::cl::value_desc("int"), llvm::cl::ValueRequired,
                  llvm::cl::Hidden);

static llvm::cl::opt<seahorn::CVerboseOpt, true, llvm::cl::parser<unsigned>>
    CrabVerbose("cverbose", llvm::cl::desc("Enable crab verbose messages"),
                llvm::cl::location(seahorn::cverbose),
                llvm::cl::value_desc("uint"));

static llvm::cl::opt<std::string>
    InputFilename(llvm::cl::Positional,
                  llvm::cl::desc("<input LLVM bitcode file>"),
                  llvm::cl::Required, llvm::cl::value_desc("filename"));

static llvm::cl::opt<std::string>
    OutputFilename("o", llvm::cl::desc("Override output filename"),
                   llvm::cl::init(""), llvm::cl::value_desc("filename"));

static llvm::cl::opt<std::string>
    AsmOutputFilename("oll", llvm::cl::desc("Output analyzed bitcode"),
                      llvm::cl::init(""), llvm::cl::value_desc("filename"));

static llvm::cl::opt<std::string> DefaultDataLayout(
    "default-data-layout",
    llvm::cl::desc("data layout string to use if not specified by module"),
    llvm::cl::init(""), llvm::cl::value_desc("layout-string"));

static llvm::cl::opt<bool> InlineAll("horn-inline-all",
                                     llvm::cl::desc("Inline all functions"),
                                     llvm::cl::init(false));

static llvm::cl::opt<bool> Solve("horn-solve",
                                 llvm::cl::desc("Run Horn solver"),
                                 llvm::cl::init(false));

static llvm::cl::opt<bool> Crab("horn-crab",
                                llvm::cl::desc("Use Crab invariants"),
                                llvm::cl::init(false));

static llvm::cl::opt<bool> PrintStats("horn-stats",
                                      llvm::cl::desc("Print statistics"),
                                      llvm::cl::init(false));

static llvm::cl::opt<bool>
    Cex("horn-cex-pass", llvm::cl::desc("Produce detailed counterexample"),
        llvm::cl::init(false));

static llvm::cl::opt<bool>
    KeepShadows("keep-shadows",
                llvm::cl::desc("Do not strip shadow.mem functions"),
                llvm::cl::init(false), llvm::cl::Hidden);

static llvm::cl::opt<bool>
    Bmc("horn-bmc",
        llvm::cl::desc(
            "Use BMC. Currently restricted to intra-procedural analysis"),
        llvm::cl::init(false));

static llvm::cl::opt<bool>
    NondetInit("horn-nondet-undef",
               llvm::cl::desc("Replace all undef with non-determinism"),
               llvm::cl::init(false));

// Available BMC engines
enum class BmcEngineKind { mono_bmc, path_bmc };

static llvm::cl::opt<BmcEngineKind>
    BmcEngine("horn-bmc-engine", llvm::cl::desc("Choose BMC engine"),
              llvm::cl::values(clEnumValN(BmcEngineKind::mono_bmc, "mono",
                                          "Solve a single formula"),
                               clEnumValN(BmcEngineKind::path_bmc, "path",
                                          "Based on path enumeration")),
              llvm::cl::init(BmcEngineKind::mono_bmc));

static llvm::cl::opt<bool>
    BoogieOutput("boogie", llvm::cl::desc("Translate llvm bitcode to boogie"),
                 llvm::cl::init(false));

static llvm::cl::opt<bool> OneAssumePerBlock(
    "horn-one-assume-per-block",
    llvm::cl::desc(
        "Make sure there is at most one call to verifier.assume per block"),
    llvm::cl::init(false));

static llvm::cl::opt<bool>
    UnifyAssumes("horn-unify-assumes",
                 llvm::cl::desc("One assume to rule them all"),
                 llvm::cl::init(false));

static llvm::cl::opt<bool> HoudiniInv(
    "horn-houdini",
    llvm::cl::desc("Use Houdini algorithm to generate inductive invariants"),
    llvm::cl::init(false));

static llvm::cl::opt<bool>
    PredAbs("horn-pred-abs",
            llvm::cl::desc(
                "Use Predicate Abstraction to generate inductive invariants"),
            llvm::cl::init(false));

static llvm::cl::opt<bool>
    MemDot("mem-dot",
           llvm::cl::desc(
               "Print SeaHorn Dsa memory graph of a function to dot format"),
           llvm::cl::init(false));

static llvm::cl::opt<bool>
    LowerGlobalInitializers("lower-gv-init",
                            llvm::cl::desc("Lower some global initializers"),
                            llvm::cl::init(true));

static llvm::cl::opt<bool> EvalBranchSentinelOpt(
    "eval-branch-sentinel",
    llvm::cl::desc("Evaluate intrinsics added by AddBranchSentinel pass."),
    llvm::cl::init(false));

// removes extension from filename if there is one
std::string getFileName(const std::string &str) {
  std::string filename = str;
  size_t lastdot = str.find_last_of(".");
  if (lastdot != std::string::npos)
    filename = str.substr(0, lastdot);
  return filename;
}

int main(int argc, char **argv) {
  seahorn::ScopedStats _st("seahorn_total");

  llvm::llvm_shutdown_obj shutdown; // calls llvm_shutdown() on exit
  llvm::cl::AddExtraVersionPrinter(print_seahorn_version);
  llvm::cl::ParseCommandLineOptions(
      argc, argv, "SeaHorn -- LLVM bitcode to Horn/SMT2 transformation\n");

  llvm::sys::PrintStackTraceOnErrorSignal(argv[0]);
  llvm::PrettyStackTraceProgram PSTP(argc, argv);
  llvm::EnableDebugBuffering = true;

  std::error_code error_code;
  llvm::SMDiagnostic err;
  llvm::LLVMContext context;
  std::unique_ptr<llvm::Module> module;
  std::unique_ptr<llvm::ToolOutputFile> output;
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

  if (!OutputFilename.empty())
    output = std::make_unique<llvm::ToolOutputFile>(
        OutputFilename.c_str(), error_code, llvm::sys::fs::F_None);

  if (error_code) {
    if (llvm::errs().has_colors())
      llvm::errs().changeColor(llvm::raw_ostream::RED);
    llvm::errs() << "error: Could not open " << OutputFilename << ": "
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
  llvm::initializeTransformUtils(Registry);
  llvm::initializeScalarOpts(Registry);
  llvm::initializeIPO(Registry);
  llvm::initializeCallGraphWrapperPassPass(Registry);
  llvm::initializeCallGraphPrinterLegacyPassPass(Registry);
  llvm::initializeCallGraphViewerPass(Registry);
  // XXX: not sure if needed anymore
  llvm::initializeGlobalsAAWrapperPassPass(Registry);

  llvm::initializeDsaAnalysisPass(Registry);
  llvm::initializeRemovePtrToIntPass(Registry);
  llvm::initializeDsaInfoPassPass(Registry);
  llvm::initializeAllocSiteInfoPass(Registry);
  llvm::initializeCompleteCallGraphPass(Registry);
  llvm::initializeAnnotation2MetadataLegacyPass(Registry);
  llvm::initializeGeneratePartialFnPassPass(Registry);
  // add an appropriate DataLayout instance for the module
  const llvm::DataLayout *dl = &module->getDataLayout();
  if (!dl && !DefaultDataLayout.empty()) {
    module->setDataLayout(DefaultDataLayout);
    dl = &module->getDataLayout();
  }

  assert(dl && "Could not find Data Layout for the module");

  pass_manager.add(llvm_seahorn::createAnnotation2MetadataLegacyPass());
  pass_manager.add(seahorn::createSeaBuiltinsWrapperPass());
  // turn all functions internal so that we can inline them if requested
  auto PreserveMain = [=](const llvm::GlobalValue &GV) {
    return GV.getName() == "main";
  };
  pass_manager.add(llvm::createInternalizePass(PreserveMain));
  pass_manager.add(llvm::createGlobalDCEPass()); // kill unused internal global
  pass_manager.add(seahorn::createGeneratePartialFnPass());

  if (InlineAll) {
    pass_manager.add(seahorn::createMarkInternalInlinePass());
    pass_manager.add(llvm::createAlwaysInlinerLegacyPass());
    pass_manager.add(
        llvm::createGlobalDCEPass()); // kill unused internal global
  }
  pass_manager.add(new seahorn::RemoveUnreachableBlocksPass());

  pass_manager.add(seahorn::createPromoteMallocPass());
  pass_manager.add(seahorn::createPromoteVerifierCallsPass());

  // -- attempt to lower any left sea.is_dereferenceable()
  // -- they might be preventing some register promotion
  pass_manager.add(seahorn::createLowerIsDerefPass());

  pass_manager.add(llvm::createPromoteMemoryToRegisterPass());
  pass_manager.add(llvm::createDeadInstEliminationPass());
  pass_manager.add(llvm::createLowerSwitchPass());
  // lowers constant expressions to instructions
  pass_manager.add(new seahorn::LowerCstExprPass());
  pass_manager.add(llvm::createDeadCodeEliminationPass());

  pass_manager.add(llvm::createUnifyFunctionExitNodesPass());

  // -- it invalidates DSA passes so it should be run before
  // -- ShadowMem
  pass_manager.add(llvm::createGlobalDCEPass()); // kill unused internal global

  // -- initialize any global variables that are left
  if (LowerGlobalInitializers) {
    pass_manager.add(new seahorn::LowerGvInitializers());
    pass_manager.add(llvm::createFunctionInliningPass());
  }

  pass_manager.add(seadsa::createRemovePtrToIntPass());

  // XXX If not BMC and not BoogieOutput then we are in Horn mode
  // XXX This needs to be cleaned up ...
  if (!Bmc && !BoogieOutput)
    // in CHC mode, rewrite all loops with constant trip count to make trip
    // count symbolic This does not change the semantics (i.e., is exact), but
    // hides the constants from CHC solver
    // XXX enabled by default. Currently, no flag to disable
    pass_manager.add(seahorn::createSymbolizeConstantLoopBoundsPass());

  if (NondetInit)
    pass_manager.add(seahorn::createNondetInitPass());
  pass_manager.add(seahorn::createSeaDsaShadowMemPass());

  // Preceding passes may introduce overflow intrinsics. This is undesirable if
  // we are not in BMC mode.
  if (!Bmc)
    pass_manager.add(seahorn::createLowerArithWithOverflowIntrinsicsPass());

  pass_manager.add(new seahorn::RemoveUnreachableBlocksPass());
  pass_manager.add(seahorn::createStripLifetimePass());
  pass_manager.add(seahorn::createDeadNondetElimPass());

  if (OneAssumePerBlock) {
    // -- it must be called after all the cfg simplifications
    pass_manager.add(seahorn::createOneAssumePerBlockPass());
  }

  if (UnifyAssumes) {
    pass_manager.add(seahorn::createUnifyAssumesPass());
  }
  // #ifdef HAVE_CLAM
  //   if (Crab && !BoogieOutput) {
  //     /// -- insert invariants in the bitecode
  //     pass_manager.add(new crab_llvm::InsertInvariants());
  //     /// -- simplify invariants added in the bitecode
  //     // pass_manager.add (seahorn::createInstCombine ());
  //   }
  // #endif

  // --- verify if an undefined value can be read
  pass_manager.add(seahorn::createCanReadUndefPass());
  if (EvalBranchSentinelOpt) {
    initializeEvalBranchSentinelPassPass(Registry);
    pass_manager.add(seahorn::createEvalBranchSentinelPassPass());
  }
  // Z3_open_log("log.txt");

  if (!Bmc && !BoogieOutput) {
    pass_manager.add(new seahorn::HornifyModule());
    if (!OutputFilename.empty()) {
      // -- XXX we dump the horn clauses into a file *before* we strip
      // -- shadows. Otherwise, HornWrite can crash.
      pass_manager.add(new seahorn::HornWrite(output->os()));
    }
  }

  // FIXME: if StripShadowMemPass () is executed then DsaPrinterPass
  // crashes because the callgraph has not been updated so it can
  // access to a callsite for which the callee function is a null
  // pointer corresponding to a stripped shadow memory function. The
  // solution for now is to make sure that DsaPrinterPass is called
  // before StripShadowMemPass. A better solution is to make sure that
  // createStripShadowMemPass updates the callgraph.
  if (MemDot) {
    pass_manager.add(seadsa::createDsaPrinterPass());
  }

  if (!AsmOutputFilename.empty()) {
    if (!KeepShadows) {
      pass_manager.add(new seahorn::NameValues());
      // -- XXX might destroy names using by HornSolver later on.
      // -- XXX it is probably dangerous to strip shadows and solve at the
      // same
      //    time.
      //
      // -- We use the same pass to remove shadow memory instructions
      //    when generated by llvm dsa.
      pass_manager.add(seahorn::createStripShadowMemPass());
      if (Bmc || BoogieOutput || HoudiniInv || PredAbs || Solve) {
        ERR << "Option --keep-shadows=false is not compatible with any of "
               "the "
               "solving options";
        std::exit(1);
      }
    }
    pass_manager.add(createPrintModulePass(asmOutput->os()));
  }

  if (Bmc) {
    llvm::raw_ostream *out = nullptr;
    if (!OutputFilename.empty())
      out = &output->os();

    switch (BmcEngine) {
    case BmcEngineKind::path_bmc:
      pass_manager.add(seahorn::createPathBmcPass(out, Solve));
      break;
    case BmcEngineKind::mono_bmc:
    default:
      pass_manager.add(seahorn::createBmcPass(out, Solve));
    }

  } else if (BoogieOutput) {
    llvm::raw_ostream *out = nullptr;
    if (!OutputFilename.empty()) {
      out = &output->os();
    } else {
      out = &llvm::outs();
    }
    pass_manager.add(seahorn::createBoogieWriterPass(out, Crab));
  } else {
    if (HoudiniInv || PredAbs || Solve) {
      if (Crab) {
        pass_manager.add(seahorn::createLoadCrabPass());
      }
    }
    if (HoudiniInv)
      pass_manager.add(new seahorn::HoudiniPass());
    if (PredAbs)
      pass_manager.add(new seahorn::PredicateAbstraction());
    if (Solve) {
      pass_manager.add(new seahorn::HornSolver());
      if (Cex)
        pass_manager.add(new seahorn::HornCex());
    }
  }

  pass_manager.run(*module.get());

  if (!AsmOutputFilename.empty())
    asmOutput->keep();
  if (!OutputFilename.empty())
    output->keep();
  if (PrintStats)
    seahorn::Stats::PrintBrunch(llvm::outs());
  return 0;
}
