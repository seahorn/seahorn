#define DEBUG_TYPE "name-values"

#include "seahorn/Transforms/Utils/NameValues.hh"

#include "llvm/IR/BasicBlock.h"
#include "llvm/IR/Instructions.h"
#include "llvm/IR/PassManager.h"
#include "llvm/Support/Debug.h"
#include "llvm/Support/raw_ostream.h"
#include "llvm/IR/IntrinsicInst.h"
#include "llvm/IR/DebugInfoMetadata.h"

#include "seahorn/Support/SeaDebug.h"
#include <boost/algorithm/string/predicate.hpp>
#include <boost/tokenizer.hpp>

using namespace llvm;

namespace seahorn {
char NameValues::ID = 0;

bool NameValues::runOnModule(Module &M) {

  for (Module::iterator FI = M.begin(), E = M.end(); FI != E; ++FI) {
    if (!(*FI).isDeclaration())
      runOnFunction(*FI);
  }
  return false;
}

static std::string sanitizeName(std::string name) {
  std::replace(name.begin(), name.end(), '-', '_'); // replace all '-' to '_'
  return name;
}

bool NameValues::runOnFunction(Function &F) {
  LOG("nv", errs() << "Running on: " << F.getName() << "\n";);

  // -- print to string
  std::string funcAsm;
  raw_string_ostream out(funcAsm);
  out << F;
  out.flush();

  typedef boost::tokenizer<boost::char_separator<char>> tokenizer;
  boost::char_separator<char> nl_sep("\n");
  boost::char_separator<char> sp_sep(" :\t%@");

  tokenizer lines(funcAsm, nl_sep);
  tokenizer::iterator line_iter = lines.begin();

  // -- skip function attributes
  if (boost::starts_with(*line_iter, "; Function Attrs:"))
    ++line_iter;

  // -- skip function definition line
  ++line_iter;

  for (Function::iterator BI = F.begin(), BE = F.end();
       BI != BE && line_iter != lines.end(); ++BI) {
    BasicBlock &BB = *BI;

    if (!BB.hasName()) {
      std::string bb_line = *line_iter;
      tokenizer names(bb_line, sp_sep);
      std::string bb_name = *names.begin();
      if (bb_name == ";")
        bb_name = "bb";
      LOG("nv", errs() << "Found BB name: " << bb_name << "\n";);

      BB.setName("_" + bb_name);
    } else {
      BB.setName(sanitizeName(BB.getName()));
    }

    ++line_iter;

    for (BasicBlock::iterator II = BB.begin(), IE = BB.end();
         II != IE && line_iter != lines.end(); ++II) {
      Instruction &I = *II;

      if (!I.hasName() && !(I.getType()->isVoidTy())) {
        std::string inst_line = *line_iter;

        tokenizer names(inst_line, sp_sep);
        std::string inst_name = *names.begin();
        LOG("nv", errs() << "Found instruction name: " << inst_name << "\n");

        I.setName("_" + inst_name);
      } else if (DbgValueInst *dbgVal = dyn_cast<DbgValueInst>(&I)) {
        Value *val = dbgVal->getValue();
        if (val && isa<Argument>(val) && !val->hasName()) {
          auto *varInfo = dbgVal->getVariable();
          if (varInfo) val->setName(sanitizeName(varInfo->getName()));
        }
      } else {
        if (I.hasName() && !I.getType()->isVoidTy()) {
          I.setName(sanitizeName(I.getName()));
        }
      }

      ++line_iter;
    }
  }

  return false;
}

} // namespace seahorn

static llvm::RegisterPass<seahorn::NameValues> X("name-values",
                                             "Names all unnamed values");
