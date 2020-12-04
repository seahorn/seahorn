#pragma once

#include "llvm/ADT/StringRef.h"
#include "llvm/Bitcode/BitcodeWriter.h"
#include "llvm/IR/DataLayout.h"
#include "llvm/IR/IRBuilder.h"
#include "llvm/IR/LLVMContext.h"
#include "llvm/IR/ValueMap.h"
#include "llvm/IR/Verifier.h"
#include "llvm/Support/FileSystem.h"
#include "llvm/Support/ToolOutputFile.h"

#include "boost/algorithm/string/replace.hpp"

#include "seahorn/Bmc.hh"
#include "seahorn/Expr/ExprLlvm.hh"
#include "seahorn/Expr/ExprMemMap.hh"
#include "seahorn/Expr/ExprOpBinder.hh"
#include "seahorn/MemSimulator.hh"
#include "seahorn/SolverBmc.hh"
#include "seahorn/Support/SeaDebug.h"
#include "seahorn/Transforms/Instrumentation/ShadowMemDsa.hh"
#include <memory>

namespace llvm {
class TargetLibraryInfo;
class DataLayout;
class LLVMContext;
class Module;
} // namespace llvm

/*
    Converts bmc trace into a linkable LLVM IR
    with all non-det functions implemented
 */

namespace seahorn {
namespace cexGen {

using MemMap = expr::exprMemMap::ExprMemMap;

// helper functions
namespace utils {

/// \brief extract content from memory expression \p e using ExprMemMap;
/// if sucessful, store default to \p e defaultValue, special id/value pairs
/// to \p out
template <typename kv>
bool extractArrayContents(Expr e, kv &out, Expr &defaultValue);

} // namespace utils

template <class Trace> class CexExeGenerator {
  Trace &m_trace;
  const DataLayout &m_dl;
  const TargetLibraryInfo &m_tli;
  LLVMContext &m_context;
  std::unique_ptr<Module> m_harness;

  // map function calls to return value(s)
  ValueMap<const Function *, ExprVector> m_func_val_map;
  // list of <start addr, size> of havoc pointers
  std::vector<std::pair<Expr, Expr>> m_memhavoc_args;

  /// \brief fills m_memhavoc_args and m_func_val_map
  void storeMemHavoc(unsigned loc, const Function *func, ImmutableCallSite cs,
                     ImmutableCallSite prevCS);

  /// \brief fills func val map, dsa data and memhavoc ptr info
  void storeDataFromTrace();

  /// \brief: Given llvm::Function \p func and a list of return values (Expr)
  /// \p values in order of execution, convert \p values to a constant array,
  /// implement \p func to return items in array in order per invocation
  void buildNonDetFunction(const Function *func, ExprVector &values);

  void buildMemhavoc(const Function *func, ExprVector &values);

  /* build nd functions with primitive type return values, memhavoc and
     shadow.mem.init */
  void buildCexModule();

  /// \brief converts Expr \p e into LLVM Constant with LLVM Type \p ty
  Constant *exprToConstant(Type *ty, Expr e);

  /// \brief extract default value and special id-val pairs from Expr encoding
  /// of a shadow mem segment \p segment using ExprMemMap; returns a
  /// ConstantArray of length \p size divided by content width, filled with
  /// default and special values
  Constant *exprToMemSegment(Expr segment, Expr startAddr, Expr size);

public:
  CexExeGenerator(Trace &trace, const DataLayout &dl,
                  const TargetLibraryInfo &tli, LLVMContext &context)
      : m_trace(trace), m_dl(dl), m_tli(tli), m_context(context) {
    storeDataFromTrace();
    buildCexModule();
  }

  void saveCexModuleToFile(llvm::StringRef CexFile);
};

} // namespace cexGen
} // namespace seahorn
