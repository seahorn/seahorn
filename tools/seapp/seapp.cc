// Derived from https://github.com/smackers/smack/blob/master/tools/smack/smack.cpp
//
// Copyright (c) 2013 Pantazis Deligiannis (p.deligiannis@imperial.ac.uk)
// This file is distributed under the MIT License. See LICENSE for details.
//

///
// SeaPP-- LLVM bitcode Pre-Processor for Verification
///
#include "llvm/LinkAllPasses.h"
#include "llvm/PassManager.h"
#include "llvm/IR/LLVMContext.h"
#include "llvm/IR/Module.h"
#include "llvm/IRReader/IRReader.h"
#include "llvm/Support/CommandLine.h"
#include "llvm/Support/Debug.h"
#include "llvm/Support/ManagedStatic.h"
#include "llvm/Support/PrettyStackTrace.h"
#include "llvm/Support/Signals.h"
#include "llvm/Support/SourceMgr.h"
#include "llvm/Support/ToolOutputFile.h"
#include "llvm/Support/raw_ostream.h"
#include "llvm/Support/FileSystem.h"

#include "llvm/Transforms/IPO.h"
#include "llvm/Bitcode/ReaderWriter.h"
#include "llvm/Bitcode/BitcodeWriterPass.h"

#include "llvm/IR/Verifier.h"

#include "seahorn/Passes.hh"

#include "seahorn/Transforms/Scalar/PromoteVerifierCalls.hh"
#include "seahorn/Transforms/Utils/RemoveUnreachableBlocksPass.hh"
#include "seahorn/Transforms/Scalar/LowerGvInitializers.hh"

#include "seahorn/Analysis/CanAccessMemory.hh"
#include "seahorn/Transforms/Scalar/LowerCstExpr.hh"
#include "seahorn/Transforms/Instrumentation/MixedSemantics.hh"
#include "seahorn/Transforms/Instrumentation/BufferBoundsCheck.hh"
#include "seahorn/Transforms/Instrumentation/NullCheck.hh"

#include "llvm_seahorn/Transforms/Scalar.h"

#include "ufo/Smt/EZ3.hh"
#include "ufo/Passes/NameValues.hpp"
#include "ufo/Stats.hh"

#include "seahorn/config.h"

void print_seapp_version()
{
  llvm::outs () << "SeaHorn (http://seahorn.github.io/):\n"
                << "  SeaPP version " << SEAHORN_VERSION_INFO << "\n";
}


static llvm::cl::opt<std::string>
InputFilename(llvm::cl::Positional, llvm::cl::desc("<input LLVM bitcode file>"),
              llvm::cl::Required, llvm::cl::value_desc("filename"));

static llvm::cl::opt<std::string>
OutputFilename("o", llvm::cl::desc("Override output filename"),
               llvm::cl::init(""), llvm::cl::value_desc("filename"));

static llvm::cl::opt<bool>
OutputAssembly("S", llvm::cl::desc("Write output as LLVM assembly"));

static llvm::cl::opt<std::string>
DefaultDataLayout("default-data-layout",
                  llvm::cl::desc("data layout string to use if not specified by module"),
                  llvm::cl::init(""), llvm::cl::value_desc("layout-string"));

static llvm::cl::opt<bool>
InlineAll ("horn-inline-all", llvm::cl::desc ("Inline all functions"),
           llvm::cl::init (false));

static llvm::cl::opt<bool>
InlineAllocFn ("horn-inline-allocators", 
               llvm::cl::desc ("Inline functions that allocate or deallocate memory"),
               llvm::cl::init (false));

static llvm::cl::opt<bool>
InlineConstructFn ("horn-inline-constructors", 
                  llvm::cl::desc ("Inline C++ constructors and destructors"),
                  llvm::cl::init (false));

static llvm::cl::opt<bool>
CutLoops ("horn-cut-loops", llvm::cl::desc ("Cut all natural loops"),
           llvm::cl::init (false));


static llvm::cl::opt<bool>
SymbolizeLoops ("horn-symbolize-loops", 
               llvm::cl::desc ("Convert constant loop bounds into symbolic bounds"),
               llvm::cl::init (false));

static llvm::cl::opt<bool>
SimplifyPointerLoops ("simplify-pointer-loops", 
               llvm::cl::desc ("Simplify loops that iterate over pointers"),
               llvm::cl::init (false));

static llvm::cl::opt<bool>
UnfoldLoopsForDsa ("unfold-loops-for-dsa", 
               llvm::cl::desc ("Unfold the first loop iteration if useful for DSA analysis"),
               llvm::cl::init (false));

static llvm::cl::opt<bool>
NullChecks ("null-check", 
     llvm::cl::desc ("Insert null-dereference checks"), 
     llvm::cl::init (false));

enum ArrayBoundsChecksEncoding {NONE=0, LOCAL=1, GLOBAL=2, GLOBAL_C=3};
static llvm::cl::opt<enum ArrayBoundsChecksEncoding>
ArrayBoundsChecks("abc",
 llvm::cl::desc ("Insert array bounds checks"),
 llvm::cl::values (
	clEnumValN (NONE    , "none"    , "No array bounds check"),
	clEnumValN (LOCAL   , "local"   , "Use local encoding (each pointer individually)"),
	clEnumValN (GLOBAL  , "global"  , "Use global encoding"),
	clEnumValN (GLOBAL_C, "global-c", "Use global encoding by calling C-defined functions"),
	clEnumValEnd),
 llvm::cl::init (NONE));

static llvm::cl::opt<bool>
EnumVerifierCalls ("enum-verifier-calls", 
     llvm::cl::desc ("Assign a unique identifier to each call to verifier.error"), 
     llvm::cl::init (false));

static llvm::cl::opt<bool>
MixedSem ("horn-mixed-sem", llvm::cl::desc ("Mixed-Semantics Transformation"),
          llvm::cl::init (false));

static llvm::cl::opt<bool>
KillVaArg ("kill-vaarg", llvm::cl::desc ("Delete vaarg functions"),
           llvm::cl::init (false));

static llvm::cl::opt<bool>
StripExtern ("strip-extern", llvm::cl::desc ("Replace external functions by nondet"),
              llvm::cl::init (false));

static llvm::cl::opt<bool>
OnlyStripExtern ("only-strip-extern", llvm::cl::desc ("Replace external functions by nondet and perform no other changes"),
              llvm::cl::init (false));

static llvm::cl::opt<bool>
LowerInvoke ("lower-invoke", 
             llvm::cl::desc ("Lower all invoke instructions"),
             llvm::cl::init (false));

static llvm::cl::opt<bool>
DevirtualizeFuncs ("devirt-functions", 
                   llvm::cl::desc ("Devirtualize indirect calls using only types"),
                   llvm::cl::init (false));

static llvm::cl::opt<bool>
ExternalizeAddrTakenFuncs ("externalize-addr-taken-funcs", 
                           llvm::cl::desc ("Externalize uses of address-taken functions"),
                           llvm::cl::init (false));

static llvm::cl::opt<bool>
LowerAssert ("lower-assert", 
             llvm::cl::desc ("Replace assertions with assumptions"),
             llvm::cl::init (false));

static llvm::cl::opt<bool>
PromoteAssumptions ("promote-assumptions",
                    llvm::cl::desc ("Promote verifier.assume to llvm.assume"),
                    llvm::cl::init (true));

static llvm::cl::opt<int>
SROA_Threshold ("sroa-threshold",
                llvm::cl::desc ("Threshold for ScalarReplAggregates pass"),
                llvm::cl::init(INT_MAX));
static llvm::cl::opt<int>
SROA_StructMemThreshold ("sroa-struct",
                         llvm::cl::desc ("Structure threshold for ScalarReplAggregates"),
                         llvm::cl::init (INT_MAX));

static llvm::cl::opt<std::string>
ApiConfig("api-config",
         llvm::cl::desc("Comma separated API function calls"),
         llvm::cl::init(""), llvm::cl::value_desc("api-string"));

static llvm::cl::opt<int>
SROA_ArrayElementThreshold ("sroa-array",
                            llvm::cl::desc ("Array threshold for ScalarReplAggregates"),
                            llvm::cl::init (INT_MAX));
static llvm::cl::opt<int>
SROA_ScalarLoadThreshold ("sroa-scalar-load",
                          llvm::cl::desc ("Scalar load threshold for ScalarReplAggregates"),
                          llvm::cl::init (-1));

static llvm::cl::opt<bool>
KleeInternalize ("klee-internalize", 
                   llvm::cl::desc ("Internalizes definitions for Klee"),
                   llvm::cl::init (false));
static llvm::cl::opt<bool>
WrapMem ("wrap-mem",
         llvm::cl::desc ("Wrap memory accesses with special functions"),
         llvm::cl::init (false));

static llvm::cl::opt<bool>
StripShadowMem ("strip-shadow-mem",
         llvm::cl::desc ("Strip shadow memory functions"),
         llvm::cl::init (false));

static llvm::cl::opt<bool>
RenameNondet ("rename-nondet",
         llvm::cl::desc ("Assign a unique name to each non-determinism per call."),
         llvm::cl::init (false));

static llvm::cl::opt<bool>
AbstractMemory ("abstract-memory",
	llvm::cl::desc ("Abstract memory instructions"),
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
  llvm::llvm_shutdown_obj shutdown;  // calls llvm_shutdown() on exit
  llvm::cl::AddExtraVersionPrinter (print_seapp_version);
  llvm::cl::ParseCommandLineOptions(argc, argv,
                                    "SeaPP-- LLVM bitcode Pre-Processor for Verification\n");

  llvm::sys::PrintStackTraceOnErrorSignal();
  llvm::PrettyStackTraceProgram PSTP(argc, argv);
  llvm::EnableDebugBuffering = true;

  std::error_code error_code;
  llvm::SMDiagnostic err;
  llvm::LLVMContext &context = llvm::getGlobalContext();
  std::unique_ptr<llvm::Module> module;
  std::unique_ptr<llvm::tool_output_file> output;
  
  module = llvm::parseIRFile(InputFilename, err, context);
  if (!module)
  {
    if (llvm::errs().has_colors()) llvm::errs().changeColor(llvm::raw_ostream::RED);
    llvm::errs() << "error: "
                 << "Bitcode was not properly read; " << err.getMessage() << "\n";
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
  
  assert (dl && "Could not find Data Layout for the module");
  
  if (dl) pass_manager.add (new llvm::DataLayoutPass ());
  if (!ApiConfig.empty())
  {
      pass_manager.add(seahorn::createApiAnalysisPass(ApiConfig));
  }
  
  if (RenameNondet)
    pass_manager.add (seahorn::createRenameNondetPass ());
  else if (StripShadowMem)
    pass_manager.add (seahorn::createStripShadowMemPass ());
  else if (KleeInternalize)
    pass_manager.add (seahorn::createKleeInternalizePass ());
  else if (WrapMem)
    pass_manager.add (seahorn::createWrapMemPass ());
  else if (OnlyStripExtern) {
    pass_manager.add (seahorn::createDevirtualizeFunctionsPass ());
    pass_manager.add (seahorn::createStripUselessDeclarationsPass ());
  }
  else
  {
    // -- Externalize some user-selected functions
    pass_manager.add (seahorn::createExternalizeFunctionsPass ());

    // -- Create a main function if we do not have one.
    pass_manager.add (seahorn::createDummyMainFunctionPass ());
 
    // -- promote verifier specific functions to special names
    pass_manager.add (new seahorn::PromoteVerifierCalls ());

    // -- promote top-level mallocs to alloca
    pass_manager.add (seahorn::createPromoteMallocPass ());

    // -- turn loads from _Bool from truc to sgt
    pass_manager.add (seahorn::createPromoteBoolLoadsPass ());

    if (KillVaArg)
      pass_manager.add (seahorn::createKillVarArgFnPass ());
  
    if (StripExtern)
      pass_manager.add (seahorn::createStripUselessDeclarationsPass ());
  
    // -- mark entry points of all functions
    if (!MixedSem && !CutLoops)
      // XXX should only be ran once. need better way to ensure that.
      pass_manager.add (seahorn::createMarkFnEntryPass ());
  
    // turn all functions internal so that we can inline them if requested
    pass_manager.add (llvm::createInternalizePass (llvm::ArrayRef<const char*>("main")));
  
    // -- resolve indirect calls
    if (DevirtualizeFuncs)
      pass_manager.add (seahorn::createDevirtualizeFunctionsPass ());
  
    // -- externalize uses of address-taken functions
    if (ExternalizeAddrTakenFuncs)
      pass_manager.add (seahorn::createExternalizeAddressTakenFunctionsPass ());

    // kill internal unused code
    pass_manager.add (llvm::createGlobalDCEPass ()); // kill unused internal global
  
    // -- global optimizations
    // FIXME: for inconsistency analysis this causes problems with
    //        trivial examples.
    pass_manager.add (llvm::createGlobalOptimizerPass());
    // pass_manager.add (llvm::createGlobalOptimizerPass());
  
    // -- SSA
    pass_manager.add(llvm::createPromoteMemoryToRegisterPass());
    // -- Turn undef into nondet
    pass_manager.add (seahorn::createNondetInitPass ());
  
    // -- cleanup after SSA
    pass_manager.add (seahorn::createInstCombine ());
    pass_manager.add (llvm::createCFGSimplificationPass ());
  
    // -- break aggregates
    pass_manager.add (llvm::createScalarReplAggregatesPass (SROA_Threshold,
                                                            true,
                                                            SROA_StructMemThreshold,
                                                            SROA_ArrayElementThreshold,
                                                            SROA_ScalarLoadThreshold));
    // -- Turn undef into nondet (undef are created by SROA when it calls mem2reg)
    pass_manager.add (seahorn::createNondetInitPass ());
  
    // -- cleanup after break aggregates
    pass_manager.add (seahorn::createInstCombine ());
    pass_manager.add (llvm::createCFGSimplificationPass ());
  
    // eliminate unused calls to verifier.nondet() functions
    pass_manager.add (seahorn::createDeadNondetElimPass ());
  
    pass_manager.add(llvm::createLowerSwitchPass());
  
    pass_manager.add(llvm::createDeadInstEliminationPass());
    pass_manager.add (new seahorn::RemoveUnreachableBlocksPass ());
    
    if (LowerInvoke) 
    {
      // -- lower invoke's
      pass_manager.add(llvm::createLowerInvokePass());
      // cleanup after lowering invoke's
      pass_manager.add (llvm::createCFGSimplificationPass ());  
    }
    
    // lower arithmetic with overflow intrinsics
    pass_manager.add(seahorn::createLowerArithWithOverflowIntrinsicsPass ());
    // lower libc++abi functions
    pass_manager.add(seahorn::createLowerLibCxxAbiFunctionsPass ());
    
    // cleanup after lowering 
    pass_manager.add (seahorn::createInstCombine ());
    pass_manager.add (llvm::createCFGSimplificationPass ());
    
    if (InlineAll || InlineAllocFn || InlineConstructFn)
    {
      if (InlineAll)
        pass_manager.add (seahorn::createMarkInternalInlinePass ());
      else {
        if (InlineAllocFn)
          pass_manager.add (seahorn::createMarkInternalAllocOrDeallocInlinePass ());
        if (InlineConstructFn)
          pass_manager.add (seahorn::createMarkInternalConstructOrDestructInlinePass ());
      }
      
      pass_manager.add (llvm::createAlwaysInlinerPass ());
      pass_manager.add (llvm::createGlobalDCEPass ()); // kill unused internal global
      pass_manager.add (seahorn::createPromoteMallocPass ());
      pass_manager.add (new seahorn::RemoveUnreachableBlocksPass ());
    }
  
    pass_manager.add(llvm::createDeadInstEliminationPass());
    pass_manager.add (llvm::createGlobalDCEPass ()); // kill unused internal global
    if (!MixedSem)
      pass_manager.add (new seahorn::LowerGvInitializers ());

    pass_manager.add(llvm::createUnifyFunctionExitNodesPass ());

    if (SimplifyPointerLoops) {
      // --- simplify loops that iterate over pointers
      pass_manager.add (seahorn::createSimplifyPointerLoopsPass ());
    }

    if (UnfoldLoopsForDsa) {
      // --- help DSA to be more precise
      pass_manager.add (llvm_seahorn::createFakeLatchExitPass());
      pass_manager.add (seahorn::createUnfoldLoopForDsaPass());
    }

    if (AbstractMemory) {
      // -- abstract memory load/stores pointer operands with
      // -- non-deterministic values
      pass_manager.add (seahorn::createAbstractMemoryPass ());
      // -- abstract memory pass generates a lot of dead load/store
      // -- instructions
      pass_manager.add(llvm::createDeadInstEliminationPass());
    }
    
    if (ArrayBoundsChecks > 0) {
      // XXX ABC might run sea-dsa which requires all values have a name
      pass_manager.add (new ufo::NameValues ());
      switch (ArrayBoundsChecks) {
      case LOCAL: 
	pass_manager.add (new seahorn::LowerCstExprPass ());
	pass_manager.add (new seahorn::Local ());
	// -- Turn undef into nondet (undef might be created by Local)
	pass_manager.add (seahorn::createNondetInitPass ());
	break;
      case GLOBAL_C:
	pass_manager.add (new seahorn::GlobalCCallbacks ());
	// --- inline some special functions
	pass_manager.add (llvm::createAlwaysInlinerPass ());
	break;
      case GLOBAL:
      default : 
	pass_manager.add (new seahorn::Global ());
      }
    }
    
    if (LowerAssert) {
      pass_manager.add (seahorn::createLowerAssertPass ());
      // LowerAssert might generate some dead code 
      pass_manager.add(llvm::createDeadInstEliminationPass());
    }
    
    pass_manager.add (new seahorn::RemoveUnreachableBlocksPass ());
    if (NullChecks) {
      pass_manager.add (new seahorn::LowerCstExprPass ());
      pass_manager.add (new seahorn::NullCheck ());
    }

    
    if (!MixedSem && EnumVerifierCalls)  
    { 
      pass_manager.add (seahorn::createEnumVerifierCallsPass ());
    }
    
    pass_manager.add (new seahorn::RemoveUnreachableBlocksPass ());
    pass_manager.add (seahorn::createPromoteMallocPass ());
    pass_manager.add (llvm::createGlobalDCEPass ()); // kill unused internal global    
  
    // -- Enable function slicing
    pass_manager.add (seahorn::createSliceFunctionsPass ());
    // -- Create a main function if we sliced it away
    pass_manager.add (seahorn::createDummyMainFunctionPass ());
    
    if (SymbolizeLoops) 
    {
      pass_manager.add (seahorn::createSymbolizeConstantLoopBoundsPass ());
    }
    
    if (MixedSem)
    {
      pass_manager.add (new seahorn::MixedSemantics ());
      pass_manager.add (new seahorn::RemoveUnreachableBlocksPass ());
      pass_manager.add (seahorn::createPromoteMallocPass ());
    }
    
    if (CutLoops)
    {
      pass_manager.add (llvm::createLoopSimplifyPass ());
      pass_manager.add (llvm::createLCSSAPass ());
      pass_manager.add (seahorn::createCutLoopsPass ());
      // pass_manager.add (new seahorn::RemoveUnreachableBlocksPass ());
    }
    
    
    if (PromoteAssumptions)
      pass_manager.add (seahorn::createPromoteSeahornAssumePass ());
  }

  // --- verify if an undefined value can be read
  pass_manager.add (seahorn::createCanReadUndefPass ());
  // --- verify if bitcode is well-formed
  pass_manager.add (llvm::createVerifierPass());
  
  if (!OutputFilename.empty ()) 
  {
    if (OutputAssembly)
      pass_manager.add (createPrintModulePass (output->os ()));
    else 
      pass_manager.add (createBitcodeWriterPass (output->os ()));
  }
  
  pass_manager.run(*module.get());
  
  if (!OutputFilename.empty ()) output->keep();
  return 0;
}
