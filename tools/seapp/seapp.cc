// Derived from
// https://github.com/smackers/smack/blob/master/tools/smack/smack.cpp
//
// Copyright (c) 2013 Pantazis Deligiannis (p.deligiannis@imperial.ac.uk)
// This file is distributed under the MIT License. See LICENSE for details.
//

///
// SeaPP-- LLVM bitcode Pre-Processor for Verification
///
#include "llvm/Bitcode/BitcodeWriter.h"
#include "llvm/Bitcode/BitcodeWriterPass.h"
#include "llvm/IR/LLVMContext.h"
#include "llvm/IR/LegacyPassManager.h"
#include "llvm/IR/Module.h"
#include "llvm/IR/Verifier.h"
#include "llvm/IRReader/IRReader.h"
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

#include "llvm/IR/Verifier.h"

#include "seahorn/InitializePasses.hh"
#include "seahorn/Passes.hh"

#ifdef HAVE_LLVM_SEAHORN
#include "llvm_seahorn/Transforms/Scalar.h"
#endif

#include "seadsa/InitializePasses.hh"

#include "seahorn/Expr/Smt/EZ3.hh"
#include "seahorn/Support/SeaLog.hh"
#include "seahorn/Support/Stats.hh"
#include "seahorn/Transforms/Utils/NameValues.hh"

#include "seahorn/config.h"

void print_seapp_version(llvm::raw_ostream &OS) {
  OS << "SeaHorn (http://seahorn.github.io/):\n"
     << "  SeaPP version " << SEAHORN_VERSION_INFO << "\n";
}

static llvm::cl::opt<std::string>
    InputFilename(llvm::cl::Positional,
                  llvm::cl::desc("<input LLVM bitcode file>"),
                  llvm::cl::Required, llvm::cl::value_desc("filename"));

static llvm::cl::opt<std::string>
    OutputFilename("o", llvm::cl::desc("Override output filename"),
                   llvm::cl::init(""), llvm::cl::value_desc("filename"));

static llvm::cl::opt<bool>
    OutputAssembly("S", llvm::cl::desc("Write output as LLVM assembly"));

static llvm::cl::opt<std::string> DefaultDataLayout(
    "default-data-layout",
    llvm::cl::desc("data layout string to use if not specified by module"),
    llvm::cl::init(""), llvm::cl::value_desc("layout-string"));

static llvm::cl::opt<bool> InlineAll("horn-inline-all",
                                     llvm::cl::desc("Inline all functions"),
                                     llvm::cl::init(false));

static llvm::cl::opt<bool> InlineAllocFn(
    "horn-inline-allocators",
    llvm::cl::desc("Inline functions that allocate or deallocate memory"),
    llvm::cl::init(false));

static llvm::cl::opt<bool>
    InlineConstructFn("horn-inline-constructors",
                      llvm::cl::desc("Inline C++ constructors and destructors"),
                      llvm::cl::init(false));

static llvm::cl::opt<bool> CutLoops("horn-cut-loops",
                                    llvm::cl::desc("Cut all natural loops"),
                                    llvm::cl::init(false));
static llvm::cl::opt<unsigned>
    PeelLoops("horn-peel-loops", llvm::cl::desc("Number of iterations to peel"),
              llvm::cl::init(0));

static llvm::cl::opt<bool> SymbolizeLoops(
    "horn-symbolize-loops",
    llvm::cl::desc("Convert constant loop bounds into symbolic bounds"),
    llvm::cl::init(false));

static llvm::cl::opt<bool> SimplifyPointerLoops(
    "simplify-pointer-loops",
    llvm::cl::desc("Simplify loops that iterate over pointers"),
    llvm::cl::init(false));

static llvm::cl::opt<bool> UnfoldLoopsForDsa(
    "unfold-loops-for-dsa",
    llvm::cl::desc(
        "Unfold the first loop iteration if useful for DSA analysis"),
    llvm::cl::init(false));

static llvm::cl::opt<bool>
    NullChecks("null-check", llvm::cl::desc("Insert null-dereference checks"),
               llvm::cl::init(false));

static llvm::cl::opt<bool>
    SimpleMemoryChecks("smc", llvm::cl::desc("Insert simple memory checks"),
                       llvm::cl::init(false));

static llvm::cl::opt<bool> EnumVerifierCalls(
    "enum-verifier-calls",
    llvm::cl::desc("Assign a unique identifier to each call to verifier.error"),
    llvm::cl::init(false));

static llvm::cl::opt<bool>
    MixedSem("horn-mixed-sem", llvm::cl::desc("Mixed-Semantics Transformation"),
             llvm::cl::init(false));

static llvm::cl::opt<bool> KillVaArg("kill-vaarg",
                                     llvm::cl::desc("Delete vaarg functions"),
                                     llvm::cl::init(false));

static llvm::cl::opt<bool>
    StripExtern("strip-extern",
                llvm::cl::desc("Replace external functions by nondet"),
                llvm::cl::init(false));

static llvm::cl::opt<bool> OnlyStripExtern(
    "only-strip-extern",
    llvm::cl::desc(
        "Replace external functions by nondet and perform no other changes"),
    llvm::cl::init(false));

static llvm::cl::opt<bool>
    LowerInvoke("lower-invoke", llvm::cl::desc("Lower all invoke instructions"),
                llvm::cl::init(true));

static llvm::cl::opt<bool>
    LowerGlobalInitializers("lower-gv-init",
                            llvm::cl::desc("Lower some global initializers"),
                            llvm::cl::init(true));

static llvm::cl::opt<bool> DevirtualizeFuncs(
    "devirt-functions",
    llvm::cl::desc("Devirtualize indirect calls "
                   "(disabled by default). "
                   "If enabled then use "
                   "--devirt-functions-method=types|sea-dsa to choose method."),
    llvm::cl::init(false));

static llvm::cl::opt<bool> ExternalizeAddrTakenFuncs(
    "externalize-addr-taken-funcs",
    llvm::cl::desc("Externalize uses of address-taken functions"),
    llvm::cl::init(false));

static llvm::cl::opt<bool>
    LowerAssert("lower-assert",
                llvm::cl::desc("Replace assertions with assumptions"),
                llvm::cl::init(false));

static llvm::cl::opt<bool>
    PromoteAssumptions("promote-assumptions",
                       llvm::cl::desc("Promote verifier.assume to llvm.assume"),
                       llvm::cl::init(false));

// static llvm::cl::opt<int>
//     SROA_Threshold("sroa-threshold",
//                    llvm::cl::desc("Threshold for ScalarReplAggregates pass"),
//                    llvm::cl::init(INT_MAX));
// static llvm::cl::opt<int> SROA_StructMemThreshold(
//     "sroa-struct",
//     llvm::cl::desc("Structure threshold for ScalarReplAggregates"),
//     llvm::cl::init(INT_MAX));

// static llvm::cl::opt<int> SROA_ArrayElementThreshold(
//     "sroa-array", llvm::cl::desc("Array threshold for ScalarReplAggregates"),
//     llvm::cl::init(INT_MAX));
// static llvm::cl::opt<int> SROA_ScalarLoadThreshold(
//     "sroa-scalar-load",
//     llvm::cl::desc("Scalar load threshold for ScalarReplAggregates"),
//     llvm::cl::init(-1));

static llvm::cl::opt<bool>
    KleeInternalize("klee-internalize",
                    llvm::cl::desc("Internalizes definitions for Klee"),
                    llvm::cl::init(false));
static llvm::cl::opt<bool>
    WrapMem("wrap-mem",
            llvm::cl::desc("Wrap memory accesses with special functions"),
            llvm::cl::init(false));

static llvm::cl::opt<bool> FatBoundsCheck(
    "fat-bnd-check",
    llvm::cl::desc(
        "Instrument buffer bounds check  using extended pointer bits"),
    llvm::cl::init(false));

static llvm::cl::opt<bool>
    LowerIsDeref("lower-is-deref",
                 llvm::cl::desc("Lower sea_is_dereferenceable() calls"),
                 llvm::cl::init(false));

static llvm::cl::opt<bool>
    StripShadowMem("strip-shadow-mem",
                   llvm::cl::desc("Strip shadow memory functions"),
                   llvm::cl::init(false));

static llvm::cl::opt<bool> RenameNondet(
    "rename-nondet",
    llvm::cl::desc("Assign a unique name to each non-determinism per call."),
    llvm::cl::init(false));

static llvm::cl::opt<bool>
    AbstractMemory("abstract-memory",
                   llvm::cl::desc("Abstract memory instructions"),
                   llvm::cl::init(false));

static llvm::cl::opt<bool> NameValues(
    "name-values",
    llvm::cl::desc(
        "Run the seahorn::NameValues pass (WARNING -- can be extremely slow)"),
    llvm::cl::init(false));

static llvm::cl::opt<bool>
    InstNamer("instnamer", llvm::cl::desc("Run the llvm's instnamer pass"),
              llvm::cl::init(false));

static llvm::cl::opt<bool>
    LowerSwitch("lower-switch",
                llvm::cl::desc("Lower SwitchInstructions to branches"),
                llvm::cl::init(true));

static llvm::cl::opt<bool>
    PromoteBoolLoads("promote-bool-loads",
                     llvm::cl::desc("Promote bool loads to sgt"),
                     llvm::cl::init(true));

static llvm::cl::opt<bool> StripDebug("strip-debug",
                                      llvm::cl::desc("Strip debug info"),
                                      llvm::cl::init(false));

static llvm::cl::opt<bool> VerifyAfterAll(
    "verify-after-all",
    llvm::cl::desc("Run the verification pass after each transformation"),
    llvm::cl::init(false));

// removes extension from filename if there is one
std::string getFileName(const std::string &str) {
  std::string filename = str;
  size_t lastdot = str.find_last_of(".");
  if (lastdot != std::string::npos)
    filename = str.substr(0, lastdot);
  return filename;
}

namespace {
/// Simple wrapper around llvm::legacy::PassManager for easier debugging.
class SeaPassManagerWrapper {
  llvm::legacy::PassManager m_PM;
  int m_verifierInstanceID = 0;

public:
  SeaPassManagerWrapper() {
    if (VerifyAfterAll)
      m_PM.add(seahorn::createDebugVerifierPass(++m_verifierInstanceID,
                                                "Initial Verifier Pass"));
  }
  void add(llvm::Pass *pass) {
    m_PM.add(pass);

    if (VerifyAfterAll)
      m_PM.add(seahorn::createDebugVerifierPass(++m_verifierInstanceID,
                                                pass->getPassName()));
  }

  void run(llvm::Module &m) { m_PM.run(m); }

  llvm::legacy::PassManager &getPassManager() { return m_PM; }
};
} // namespace

int main(int argc, char **argv) {
  llvm::llvm_shutdown_obj shutdown; // calls llvm_shutdown() on exit
  llvm::cl::AddExtraVersionPrinter(print_seapp_version);
  llvm::cl::ParseCommandLineOptions(
      argc, argv, "SeaPP-- LLVM bitcode Pre-Processor for Verification\n");

  llvm::sys::PrintStackTraceOnErrorSignal(argv[0]);
  llvm::PrettyStackTraceProgram PSTP(argc, argv);
  llvm::EnableDebugBuffering = true;

  std::error_code error_code;
  llvm::SMDiagnostic err;
  static llvm::LLVMContext context;
  std::unique_ptr<llvm::Module> module;
  std::unique_ptr<llvm::ToolOutputFile> output;

  module = llvm::parseIRFile(InputFilename, err, context);
  if (!module) {
    if (llvm::errs().has_colors())
      llvm::errs().changeColor(llvm::raw_ostream::RED);
    llvm::errs() << "error: "
                 << "Bitcode was not properly read; " << err.getMessage()
                 << "\n";
    if (llvm::errs().has_colors())
      llvm::errs().resetColor();
    return 3;
  }

  if (llvm::verifyModule(*module, &(llvm::errs()))) {
    ERR << "BROKEN INPUT IR\n";
    return 4;
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

  SeaPassManagerWrapper pm_wrapper;
  llvm::PassRegistry &Registry = *llvm::PassRegistry::getPassRegistry();
  llvm::initializeCore(Registry);
  llvm::initializeTransformUtils(Registry);
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
  llvm::initializeAllocWrapInfoPass(Registry);
  llvm::initializeDsaLibFuncInfoPass(Registry);

  llvm::initializeCompleteCallGraphPass(Registry);

  // add an appropriate DataLayout instance for the module
  const llvm::DataLayout *dl = &module->getDataLayout();
  if (!dl && !DefaultDataLayout.empty()) {
    module->setDataLayout(DefaultDataLayout);
    dl = &module->getDataLayout();
  }

  assert(dl && "Could not find Data Layout for the module");

  pm_wrapper.add(seahorn::createSeaBuiltinsWrapperPass());

  if (RenameNondet)
    // -- ren-nondet utility pass
    pm_wrapper.add(seahorn::createRenameNondetPass());
  else if (StripShadowMem)
    // -- strips shadows. Useful for debugging
    pm_wrapper.add(seahorn::createStripShadowMemPass());
  else if (KleeInternalize)
    // -- internalize external definitions to make klee happy
    // -- useful for preparing seahorn bitcode to be used with KLEE
    pm_wrapper.add(seahorn::createKleeInternalizePass());
  else if (WrapMem)
    // -- wraps memory instructions with a custom function
    // -- not actively used. part of cex replaying
    pm_wrapper.add(seahorn::createWrapMemPass());
  else if (OnlyStripExtern) {
    // -- remove useless declarations
    pm_wrapper.add(seahorn::createDevirtualizeFunctionsPass());
    pm_wrapper.add(seahorn::createStripUselessDeclarationsPass());
  } else if (MixedSem) {
    // -- apply mixed semantics
    assert(LowerSwitch && "Lower switch must be enabled");
    pm_wrapper.add(llvm::createLowerSwitchPass());
    pm_wrapper.add(seahorn::createPromoteVerifierCallsPass());
    pm_wrapper.add(seahorn::createCanFailPass());
    pm_wrapper.add(seahorn::createMixedSemanticsPass());
    pm_wrapper.add(seahorn::createRemoveUnreachableBlocksPass());
    pm_wrapper.add(seahorn::createPromoteMallocPass());
  } else if (CutLoops || PeelLoops > 0) {
    // -- cut loops to turn a program into loop-free program
    pm_wrapper.add(llvm::createLoopSimplifyPass());
    pm_wrapper.add(llvm::createLoopSimplifyCFGPass());
    pm_wrapper.add(llvm_seahorn::createLoopRotatePass(/*1023*/));
    pm_wrapper.add(llvm::createLCSSAPass());
    if (PeelLoops > 0)
      pm_wrapper.add(seahorn::createLoopPeelerPass(PeelLoops));
    if (CutLoops) {
      pm_wrapper.add(seahorn::createBackEdgeCutterPass());
      // -- disabled. back-edge-cutter should be more robust
      // pm_wrapper.add(seahorn::createCutLoopsPass());
    }
    // pm_wrapper.add (new seahorn::RemoveUnreachableBlocksPass ());
  }
  // checking for simple instances of memory safety. WIP
  else if (SimpleMemoryChecks) {
    pm_wrapper.add(llvm::createPromoteMemoryToRegisterPass());
    pm_wrapper.add(seahorn::createSimpleMemoryCheckPass());
  }
  // null deref check. WIP. Not used.
  else if (NullChecks) {
    pm_wrapper.add(seahorn::createLowerCstExprPass());
    pm_wrapper.add(seahorn::createNullCheckPass());
  } else if (FatBoundsCheck) {
    initializeFatBufferBoundsCheckPass(Registry);
    pm_wrapper.add(seahorn::createFatBufferBoundsCheckPass());
  } else if (LowerIsDeref) {
    pm_wrapper.add(seahorn::createLowerIsDerefPass());
  }
  // default pre-processing pipeline
  else {
    // -- Externalize some user-selected functions
    pm_wrapper.add(seahorn::createExternalizeFunctionsPass());

    // -- Create a main function if we do not have one.
    pm_wrapper.add(seahorn::createDummyMainFunctionPass());

    // -- promote verifier specific functions to special names
    pm_wrapper.add(seahorn::createPromoteVerifierCallsPass());

    // -- promote top-level mallocs to alloca
    pm_wrapper.add(seahorn::createPromoteMallocPass());

    // -- turn loads from _Bool from truc to sgt
    if (PromoteBoolLoads)
      pm_wrapper.add(seahorn::createPromoteBoolLoadsPass());

    if (KillVaArg)
      pm_wrapper.add(seahorn::createKillVarArgFnPass());

    if (StripExtern)
      pm_wrapper.add(seahorn::createStripUselessDeclarationsPass());

    // -- mark entry points of all functions
    pm_wrapper.add(seahorn::createMarkFnEntryPass());

    // turn all functions internal so that we can inline them if requested
    auto PreserveMain = [=](const llvm::GlobalValue &GV) {
      return GV.getName() == "main" || GV.getName() == "bcmp";
    };
    pm_wrapper.add(llvm::createInternalizePass(PreserveMain));

    if (LowerInvoke) {
      // -- lower invoke's
      pm_wrapper.add(llvm::createLowerInvokePass());
      // cleanup after lowering invoke's
      pm_wrapper.add(llvm::createCFGSimplificationPass());
    }

    // -- resolve indirect calls
    if (DevirtualizeFuncs) {
      pm_wrapper.add(llvm::createWholeProgramDevirtPass(nullptr, nullptr));
      pm_wrapper.add(seahorn::createDevirtualizeFunctionsPass());
    }

    // -- externalize uses of address-taken functions
    if (ExternalizeAddrTakenFuncs)
      pm_wrapper.add(seahorn::createExternalizeAddressTakenFunctionsPass());

    // kill internal unused code
    pm_wrapper.add(llvm::createGlobalDCEPass()); // kill unused internal global

    // -- global optimizations
    pm_wrapper.add(llvm::createGlobalOptimizerPass());

    // -- explicitly initialize globals in the beginning of main()
    if (LowerGlobalInitializers)
      pm_wrapper.add(seahorn::createLowerGvInitializersPass());

    // -- SSA
    pm_wrapper.add(llvm::createPromoteMemoryToRegisterPass());
    // -- Turn undef into nondet
    pm_wrapper.add(seahorn::createNondetInitPass());

    // -- Promote memcpy to loads-and-stores for easier alias analysis.
    pm_wrapper.add(seahorn::createPromoteMemcpyPass());

    // -- cleanup after SSA
    pm_wrapper.add(seahorn::createInstCombine());
    pm_wrapper.add(llvm::createCFGSimplificationPass());

    // -- break aggregates
    // XXX: createScalarReplAggregatesPass is not defined in llvm 5.0
    // pm_wrapper.add(llvm::createScalarReplAggregatesPass(
    //     SROA_Threshold, true, SROA_StructMemThreshold,
    //     SROA_ArrayElementThreshold, SROA_ScalarLoadThreshold));
    pm_wrapper.add(llvm::createSROAPass());
    // -- Turn undef into nondet (undef are created by SROA when it calls
    //     mem2reg)
    pm_wrapper.add(seahorn::createNondetInitPass());

    // -- cleanup after break aggregates
    pm_wrapper.add(seahorn::createInstCombine());
    pm_wrapper.add(llvm::createCFGSimplificationPass());

    // eliminate unused calls to verifier.nondet() functions
    pm_wrapper.add(seahorn::createDeadNondetElimPass());

    if (LowerSwitch)
      pm_wrapper.add(llvm::createLowerSwitchPass());

    pm_wrapper.add(llvm::createDeadInstEliminationPass());
    pm_wrapper.add(seahorn::createRemoveUnreachableBlocksPass());

    // lower arithmetic with overflow intrinsics
    pm_wrapper.add(seahorn::createLowerArithWithOverflowIntrinsicsPass());
    // lower libc++abi functions
    pm_wrapper.add(seahorn::createLowerLibCxxAbiFunctionsPass());

    // cleanup after lowering
    pm_wrapper.add(seahorn::createInstCombine());
    pm_wrapper.add(llvm::createCFGSimplificationPass());

    if (UnfoldLoopsForDsa) {
      // --- help DSA to be more precise
#ifdef HAVE_LLVM_SEAHORN
      pm_wrapper.add(llvm_seahorn::createFakeLatchExitPass());
#endif
      pm_wrapper.add(seahorn::createUnfoldLoopForDsaPass());
    }

    if (SimplifyPointerLoops) {
      // --- simplify loops that iterate over pointers
      pm_wrapper.add(seahorn::createSimplifyPointerLoopsPass());
    }

    // XXX: AG: Should not be part of standard pipeline
    if (AbstractMemory) {
      // -- abstract memory load/stores pointer operands with
      // -- non-deterministic values
      pm_wrapper.add(seahorn::createAbstractMemoryPass());
      // -- abstract memory pass generates a lot of dead load/store
      // -- instructions
      pm_wrapper.add(llvm::createDeadInstEliminationPass());
    }

    // AG: Used for inconsistency analysis
    // XXX Should be moved out of standard pp pipeline
    if (LowerAssert) {
      pm_wrapper.add(seahorn::createLowerAssertPass());
      // LowerAssert might generate some dead code
      pm_wrapper.add(llvm::createDeadInstEliminationPass());
    }
    pm_wrapper.add(seahorn::createRemoveUnreachableBlocksPass());

    // -- request seaopt to inline all functions
    if (InlineAll)
      pm_wrapper.add(seahorn::createMarkInternalInlinePass());
    else {
      // mark memory allocator/deallocators to be inlined
      if (InlineAllocFn)
        pm_wrapper.add(seahorn::createMarkInternalAllocOrDeallocInlinePass());
      // mark constructors to be inlined
      if (InlineConstructFn)
        pm_wrapper.add(
            seahorn::createMarkInternalConstructOrDestructInlinePass());
    }

    // run inliner pass
    if (InlineAll || InlineAllocFn || InlineConstructFn) {
      pm_wrapper.add(llvm::createAlwaysInlinerLegacyPass());
      pm_wrapper.add(
          llvm::createGlobalDCEPass()); // kill unused internal global
      pm_wrapper.add(seahorn::createPromoteMallocPass());
      pm_wrapper.add(seahorn::createRemoveUnreachableBlocksPass());
    }

    // -- EVERYTHING IS MORE EXPENSIVE AFTER INLINING
    // -- BEFORE SCHEDULING PASSES HERE, THINK WHETHER THEY BELONG BEFORE
    // INLINE!
    pm_wrapper.add(llvm::createDeadInstEliminationPass());
    pm_wrapper.add(llvm::createGlobalDCEPass()); // kill unused internal global
    pm_wrapper.add(llvm::createUnifyFunctionExitNodesPass());

    // -- moves loop initialization up
    // AG: After inline because cheap and loop initialization is moved higher up
    if (SymbolizeLoops)
      pm_wrapper.add(seahorn::createSymbolizeConstantLoopBoundsPass());

    // AG: Maybe should be moved before inline. Not used as far as I know.
    if (EnumVerifierCalls)
      pm_wrapper.add(seahorn::createEnumVerifierCallsPass());

    pm_wrapper.add(seahorn::createRemoveUnreachableBlocksPass());
    pm_wrapper.add(seahorn::createPromoteMallocPass());
    pm_wrapper.add(llvm::createGlobalDCEPass()); // kill unused internal global

    // -- Enable function slicing
    // AG: NOT USED. Not part of std pipeline
    pm_wrapper.add(seahorn::createSliceFunctionsPass());

    // -- Create a main function if we sliced it away
    pm_wrapper.add(seahorn::createDummyMainFunctionPass());

    // AG: Dangerous. Promotes verifier.assume() to llvm.assume()
    if (PromoteAssumptions)
      pm_wrapper.add(seahorn::createPromoteSeahornAssumePass());
  }

  if (NameValues)
    pm_wrapper.add(seahorn::createNameValuesPass());

  if (InstNamer)
    pm_wrapper.add(llvm::createInstructionNamerPass());

  if (StripDebug)
    pm_wrapper.add(llvm::createStripDeadDebugInfoPass());

  // --- verify if an undefined value can be read
  pm_wrapper.add(seahorn::createCanReadUndefPass());
  // --- verify if bitcode is well-formed
  pm_wrapper.add(llvm::createVerifierPass());

  if (!OutputFilename.empty()) {
    if (OutputAssembly)
      pm_wrapper.add(createPrintModulePass(output->os()));
    else
      pm_wrapper.add(createBitcodeWriterPass(output->os()));
  }

  pm_wrapper.run(*module.get());

  if (!OutputFilename.empty())
    output->keep();
  return 0;
}
