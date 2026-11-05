/// Export to sea-mlir (see include/seahorn/SeaMlirExport.hh).
///
/// Mapping (sea-mlir docs/design/Memory*.md):
/// - integers -> iN; pointers -> !sea.ptr<W>; memory -> one Mem-SSA chain
///   per shadow-memory region, !sea.mem<!sea.ptr<W>, i8> (byte memory),
///   every update `inplace` (shadow memory is Mem-SSA);
/// - shadow.mem.store(R, in) defines the version written by the next memory
///   instruction; shadow.mem.load(R, v) names the version the next load
///   reads; shadow.mem.trsfr.load the source of the next memcpy; i32 phis of
///   versions become memory block arguments;
/// - BMC's query (a path from entry to the return block, which earlier
///   passes make reachable only through seahorn.fail) becomes
///   `sea.assert false` before `sea.halt` in the return block;
///   `unreachable` becomes `sea.unreachable`;
/// - shadow.mem.global.init stores a global's initializer: one sea.memset
///   when every byte is one value (zeroinitializer, a splat; any size),
///   else byte by byte, up to 16 KiB, when it is plain data (integers,
///   floats, arrays, structs, zeros;
///   undef bytes stay nondet); an initializer the export cannot write
///   (pointers, constant expressions, larger than 16 KiB and not a splat,
///   or a global used without a shadow.mem.global.init) is an error, or,
///   with --horn-sea-mlir-allow-uninit-globals, a warning and the global
///   starts uninitialized;
/// - calls to external functions without a shadow-memory definition are
///   no-ops returning a nondet value (as BvOpSem2), with a warning per
///   callee;
/// - first-class aggregates (structs, arrays) -> !sea.struct;
///   insertvalue / extractvalue -> sea.struct.insert / extract chains along
///   the index path; aggregate constants -> sea.struct.create; an undef
///   aggregate (the `insertvalue undef, ...` idiom) -> sea.struct.nondet,
///   explicit nondet initialization (sea has no undef), with the defined
///   fields of a partly undef constant inserted; aggregate loads / stores:
///   error;
/// - nsw / nuw on add, sub, mul, shl become sea's no-wrap promises (the
///   VC ignores them, as SeaHorn does; sea-wrap-flags assumes or asserts
///   them);
/// - intrinsics with a sea op (min/max, bswap, fshl/fshr) map 1:1;
///   {iN, i1} = *.with.overflow becomes the plain op and a sea.uaddo / saddo /
///   ... op, which the extractvalues of the result pick; llvm.expect is its
///   argument; cttz / ctlz (a zero input is the width, also with
///   is_zero_poison) are a binary search of selects, bitreverse a concat of
///   one-bit extracts (sea has no op for them);
/// - inline assembly: only BvOpSem2's patterns (empty-body and
///   comment-only barriers, a single bswap) are recognized, here, so sea-mlir
///   never sees assembly;
/// - shadow.mem.in / shadow.mem.out (main only) have no effect.
///
/// sea_printf(fmt, ...) becomes counterexample prints (sea-mlir
/// docs/design/Print.md), which encode nothing in the VC: one strong
/// sea.print per integer or pointer argument, a tag line for a call without
/// arguments (exportPrintf).
///
/// Anything else is an error.

#include "seahorn/SeaMlirExport.hh"

#include "seahorn/Support/InlineAsmBarrier.hh"
#include "seahorn/Support/SeaDebug.h"
#include "seahorn/Support/SeaLog.hh"

#include "llvm/ADT/DenseMap.h"
#include "llvm/ADT/DenseSet.h"
#include "llvm/ADT/PostOrderIterator.h"
#include "llvm/ADT/StringExtras.h"
#include "llvm/ADT/StringSet.h"
#include "llvm/Analysis/ValueTracking.h"
#include "llvm/IR/CFG.h"
#include "llvm/IR/Constants.h"
#include "llvm/IR/DataLayout.h"
#include "llvm/IR/DebugInfoMetadata.h"
#include "llvm/IR/Dominators.h"
#include "llvm/IR/Function.h"
#include "llvm/IR/GetElementPtrTypeIterator.h"
#include "llvm/IR/IRBuilder.h"
#include "llvm/IR/InlineAsm.h"
#include "llvm/IR/InstIterator.h"
#include "llvm/IR/Instructions.h"
#include "llvm/IR/IntrinsicInst.h"
#include "llvm/IR/Intrinsics.h"
#include "llvm/IR/Module.h"
#include "llvm/IR/ModuleSlotTracker.h"
#include "llvm/Support/CommandLine.h"
#include "llvm/Support/FileSystem.h"
#include "llvm/Support/MathExtras.h"
#include "llvm/Support/MemoryBuffer.h"
#include "llvm/Support/Path.h"
#include "llvm/Support/Process.h"
#include "llvm/Support/Program.h"
#include "llvm/Support/raw_ostream.h"

#include <cstdlib>
#include <optional>

using namespace llvm;

static cl::opt<std::string> SeaMlirOut(
    "horn-sea-mlir-out",
    cl::desc("sea-mlir engine: write the exported program to this file "
             "(default: a temporary file)"),
    cl::init(""));

static cl::opt<std::string> SeaMlirLlOut(
    "horn-sea-mlir-ll-out",
    cl::desc("sea-mlir engine (debugging): write the exported LLVM module to "
             "this file and link every op's location to its instruction "
             "there (fused<\"llvm @f %bb #i\">)"),
    cl::init(""));

static cl::opt<std::string>
    SeaVcPath("horn-sea-vc", cl::desc("sea-mlir engine: the sea-vc tool"),
              cl::init("sea-vc"));

static cl::opt<bool> SeaMlirExportOnly(
    "horn-sea-mlir-export-only",
    cl::desc("sea-mlir engine: export and exit without running sea-vc; the "
             "exit status is 0 if the export succeeded, 1 otherwise"),
    cl::init(false));

static cl::opt<bool> SeaMlirAllowUninitGlobals(
    "horn-sea-mlir-allow-uninit-globals",
    cl::desc("sea-mlir export: a global initializer the export cannot "
             "write (pointers, constant expressions, a large non-splat "
             "initializer) is a warning, and the global starts "
             "uninitialized (default: an error)"),
    cl::init(false));

static cl::list<std::string>
    SeaVcArgs("horn-sea-vc-arg",
              cl::desc("sea-mlir engine: an extra argument for sea-vc"));

namespace seahorn {
/// The alignment of an object (alloca, global). LLVM's is the minimum
/// requested; SeaHorn's allocators raise every alignment to the memory
/// manager's (BvOpSem2RawMemMgr.cc:176,194,255), which is the word size
/// (BvOpSem2MemManager.cc:16): --horn-bv2-word-size, by default the pointer
/// size (BvOpSem2.cc:2847). The export states what SeaHorn's VC assumes.
static uint64_t objectAlign(llvm::Align a, unsigned ptrBytes) {
  unsigned word = 0;
  auto &opts = cl::getRegisteredOptions();
  if (auto it = opts.find("horn-bv2-word-size"); it != opts.end())
    word = static_cast<cl::opt<unsigned> *>(it->second)->getValue();
  return std::max<uint64_t>(a.value(), word ? word : ptrBytes);
}

namespace {

/// Escapes a string for an MLIR string literal (a non-printable byte as
/// \HH).
std::string quote(StringRef s) {
  std::string r = "\"";
  for (char c : s) {
    if (c == '"' || c == '\\')
      (r += '\\') += c;
    else if (isPrint(c))
      r += c;
    else
      r += "\\" + utohexstr(uint8_t(c), /*LowerCase=*/false, 2);
  }
  return r + "\"";
}

class Exporter {
public:
  Exporter(const Function &F, raw_ostream &out, SeaMlirSites &sites,
           bool llvmLinks, StringRef mlirPath)
      : F(F), DL(F.getParent()->getDataLayout()), out(out), sites(sites),
        os(body) {
    this->llvmLinks = llvmLinks;
    this->mlirPath = mlirPath.str();
    W = DL.getPointerSizeInBits();
    ptrTy = "!sea.ptr<" + std::to_string(W) + ">";
    memTy = "!sea.mem<" + ptrTy + ", i8>";
    for (const DICompileUnit *cu : F.getParent()->debug_compile_units()) {
      srcRoot = cu->getDirectory().str();
      break;
    }
  }

  bool run();

private:
  // -- diagnostics
  void error(const Twine &msg, const Value *at = nullptr) {
    std::string where;
    if (at) {
      raw_string_ostream w(where);
      w << " at: " << *at;
    }
    ERR << "sea-mlir export: " << msg << where;
    ok = false;
  }
  void warnOnce(const Twine &key, const Twine &msg) {
    if (warned.insert(key.str()).second)
      WARN << "sea-mlir export: " << msg;
  }
  /// \p gv's initializer is not written (\p why): the global would start
  /// uninitialized, which can make true facts unprovable and false ones
  /// provable. An error unless --horn-sea-mlir-allow-uninit-globals (then a
  /// warning); once per global.
  void droppedInit(const GlobalVariable &gv, const Twine &why) {
    std::string msg = ("the initializer of global " + gv.getName() +
                       " is dropped (" + why +
                       "): the global would start uninitialized")
                          .str();
    if (!warned.insert("init:" + gv.getName().str()).second)
      return;
    if (SeaMlirAllowUninitGlobals) {
      WARN << "sea-mlir export: " << msg;
      return;
    }
    error(msg + " (--horn-sea-mlir-allow-uninit-globals allows it)");
  }

  // -- names and types
  std::string fresh() { return "%v" + std::to_string(next++); }
  std::optional<std::string> type(Type *t, const Value *at);
  std::optional<std::string> vectorConstant(const llvm::Constant *c,
                                            const Instruction &at);
  std::string
  concatParts(ArrayRef<std::pair<std::string, unsigned>> parts,
              const std::string &l);
  std::string loc(const Instruction &I, bool named = true);
  bool generatedName(const Value &v) const;
  /// Source paths are relative to it: the compilation directory of the
  /// module's first compile unit.
  std::string srcRoot;
  /// --horn-sea-mlir-ll-out: link each op to its LLVM instruction.
  bool llvmLinks = false;
  std::string mlirPath;
  std::string llvmLink(const Instruction &I);
  void placePositions(std::string &text) const;
  std::unique_ptr<ModuleSlotTracker> slots;
  DenseMap<const Instruction *, std::string> links;
  std::string blockName(const BasicBlock *BB) {
    auto it = blocks.find(BB);
    if (it == blocks.end())
      it = blocks.try_emplace(BB, "^bb" + std::to_string(blocks.size())).first;
    return it->second;
  }

  // -- operands: emits code for constants and returns the operand's name
  std::optional<std::string> val(const Value *v, const Instruction &at);
  std::optional<std::string> constant(const Constant *c, const Instruction &at);
  /// A struct / array constant as sea.struct.create, or, if undef
  /// anywhere, as sea.struct.nondet plus inserts of its defined fields.
  std::optional<std::string> aggregate(const Constant *c,
                                       const Instruction &at);
  /// An integer operand converted to the pointer width (for sizes).
  std::optional<std::string> sizeVal(const Value *v, const Instruction &at);
  std::string emitConst(const APInt &v, const std::string &l) {
    std::string n = fresh();
    SmallString<32> digits;
    v.toStringUnsigned(digits);
    os << "  " << n << " = sea.const " << digits << " : i" << v.getBitWidth()
       << l << "\n";
    return n;
  }

  // -- memory
  void findMemValues();
  bool isMem(const Value *v) const { return memValues.count(v); }
  unsigned regionOf(const CallBase &cb) {
    return cast<ConstantInt>(cb.getArgOperand(0))->getZExtValue();
  }
  uint64_t site(const Instruction *I) {
    sites.inst[nextSite] = I;
    return nextSite++;
  }

  // -- instructions
  void exportBlock(const BasicBlock &BB);
  bool vectorOk(const Instruction &I);
  void exportVectorElement(const Instruction &I);
  void exportInst(const Instruction &I);
  void exportCall(const CallBase &CB);
  void exportShadow(const CallBase &CB, StringRef name);
  void exportInlineAsm(const CallBase &CB, const InlineAsm &IA);
  void exportPrintf(const CallBase &CB, const std::string &l);
  void exportMemdump(const CallBase &CB, const std::string &l);
  /// Stores the initializer of \p gv into memory version \p mem; returns
  /// the new version, or std::nullopt if the initializer is not plain data.
  std::optional<std::string> exportGlobalInit(const GlobalVariable &gv,
                                              const std::string &mem,
                                              const Instruction &at);
  /// Returns false if \p CB is not an intrinsic with a sea op.
  bool exportIntrinsic(const CallBase &CB, Intrinsic::ID id);
  /// llvm.cttz / llvm.ctlz / llvm.bitreverse, which have no sea op, in
  /// terms of existing sea ops.
  void exportBitIntrinsic(const CallBase &CB, Intrinsic::ID id);
  /// Emits the pointer arithmetic of \p gep; returns the result's name.
  std::optional<std::string> exportGep(const GEPOperator &gep,
                                       const Instruction &at);
  void exportBranch(const BasicBlock &from, const BasicBlock &to,
                    const Instruction &at, std::string &text);
  /// The version the next memory update of a region consumes and defines.
  std::optional<std::pair<std::string, const Value *>>
  takeDef(const Instruction &I);
  std::optional<std::string> takeUse(const Instruction &I);

  const Function &F;
  const DataLayout &DL;
  raw_ostream &out;
  SeaMlirSites &sites;
  std::string body;
  raw_string_ostream os;
  unsigned W;
  std::string ptrTy, memTy;
  unsigned next = 0;
  uint64_t nextSite = 0;
  bool ok = true;
  StringSet<> warned;
  DenseMap<const Value *, std::string> names;
  DenseMap<const BasicBlock *, std::string> blocks;
  DenseSet<const Value *> memValues;
  /// Globals whose initializer was exported (by shadow.mem.global.init).
  DenseSet<const GlobalVariable *> initializedGlobals;
  /// Globals whose initializer exportGlobalInit could not write.
  DenseSet<const GlobalVariable *> initFailed;
  /// The fields of {iN, i1} results of *.with.overflow intrinsics, which
  /// only extractvalue may use.
  DenseMap<const Value *, std::pair<std::string, std::string>> overflowParts;
  // shadow memory: pending definition and uses for the next memory op
  std::optional<std::pair<std::string, const Value *>> pendingDef;
  std::optional<std::string> pendingUse;
  const Value *pendingUseVersion = nullptr; // its LLVM shadow value

  std::optional<std::string> pendingTrsfr;
  /// shadow.mem.arg.ref versions before a call (sea_memdump)
  SmallVector<std::string, 1> pendingArgRefs;
};

std::optional<std::string> Exporter::type(Type *t, const Value *at) {
  if (auto *it = dyn_cast<IntegerType>(t))
    return "i" + std::to_string(it->getBitWidth());
  if (t->isPointerTy())
    return ptrTy;
  // Floating point is not modeled (as in SeaHorn's BvOpSem2): a float is
  // the bit-vector of its width; arithmetic on it is nondet (floatNondet).
  if (t->isFloatingPointTy())
    return "i" + std::to_string(t->getPrimitiveSizeInBits().getFixedValue());
  // A vector of integers is one bit-vector, lane i at bits [i*K, (i+1)*K), as
  // in SeaHorn (BvOpSem2.cc:2065-2130); only lane-agnostic instructions are
  // exported on it (vectorOk).
  if (auto *vt = dyn_cast<FixedVectorType>(t)) {
    if (auto *et = dyn_cast<IntegerType>(vt->getElementType()))
      return "i" + std::to_string(et->getBitWidth() * vt->getNumElements());
    error("vectors of non-integers are not supported", at);
    return std::nullopt;
  }
  // First-class aggregates (structs, arrays) are register structs; packing
  // does not matter: they have no layout in registers.
  if (isa<StructType, ArrayType>(t)) {
    constexpr unsigned kMaxFields = 64;
    SmallVector<Type *> fields;
    if (auto *st = dyn_cast<StructType>(t))
      fields.append(st->element_begin(), st->element_end());
    else if (cast<ArrayType>(t)->getNumElements() <= kMaxFields)
      fields.append(cast<ArrayType>(t)->getNumElements(),
                    cast<ArrayType>(t)->getElementType());
    if (fields.empty() || fields.size() > kMaxFields) {
      error("aggregate values with 0 or more than 64 fields are not "
            "supported",
            at);
      return std::nullopt;
    }
    std::vector<std::string> fs;
    for (Type *f : fields) {
      auto ft = type(f, at);
      if (!ft)
        return std::nullopt;
      fs.push_back(*ft);
    }
    return "!sea.struct<" + join(fs, ", ") + ">";
  }
  std::string s;
  raw_string_ostream ts(s);
  ts << *t;
  error("unsupported type " + s, at);
  return std::nullopt;
}

/// --horn-sea-mlir-ll-out: stands for an op's position in the output
/// (placePositions).
static constexpr const char *kPosToken = "@@SEA_MLIR_POS@@";

/// The link of \p I to the .ll file: "llvm @<function> %<block> #<i>", the
/// block as the .ll names it (its name, else its slot number), i the
/// instruction's 0-based ordinal in the block.
std::string Exporter::llvmLink(const Instruction &I) {
  auto it = links.find(&I);
  if (it != links.end())
    return it->second;
  if (!slots) {
    slots = std::make_unique<ModuleSlotTracker>(F.getParent());
    slots->incorporateFunction(F);
  }
  const BasicBlock &BB = *I.getParent();
  std::string head;
  raw_string_ostream hs(head);
  hs << "llvm ";
  F.printAsOperand(hs, false, *slots);
  hs << " ";
  BB.printAsOperand(hs, false, *slots);
  unsigned k = 0;
  for (const Instruction &J : BB)
    links[&J] = head + " #" + std::to_string(k++);
  return links[&I];
}

/// An op without a source position gets its position in the output file:
/// the MLIR parser gives an op without a location that position, but not an
/// op whose location is only the llvm link. Body line n is file line n + 2
/// (the comment and the sea.program line); the column is the op name's.
void Exporter::placePositions(std::string &text) const {
  std::string res;
  size_t lineNo = 3;
  for (StringRef rest = text; !rest.empty(); ++lineNo) {
    auto [line, tail] = rest.split('\n');
    rest = tail;
    size_t at = line.find(kPosToken);
    if (at == StringRef::npos) {
      res += line;
      res += '\n';
      continue;
    }
    size_t col = line.find_first_not_of(' ');
    if (line.substr(col).starts_with("%")) {
      size_t eq = line.find(" = ", col);
      if (eq != StringRef::npos)
        col = eq + 3;
    }
    std::string pos = quote(mlirPath) + ":" + std::to_string(lineNo) + ":" +
                      std::to_string(col + 1);
    for (; at != StringRef::npos; at = line.find(kPosToken)) {
      res += line.take_front(at);
      res += pos;
      line = line.drop_front(at + strlen(kPosToken));
    }
    res += line;
    res += '\n';
  }
  text = std::move(res);
}

/// The path of a source file: its directory and name, relative to the
/// compilation directory \p root when it lies under it, else absolute (or as
/// the debug info has it).
static std::string sourcePath(const DIFile *file, StringRef root) {
  if (!file)
    return "";
  SmallString<128> path(file->getFilename());
  if (!sys::path::is_absolute(path) && !file->getDirectory().empty()) {
    path = file->getDirectory();
    sys::path::append(path, file->getFilename());
  }
  sys::path::remove_dots(path, /*remove_dot_dot=*/true);
  if (!root.empty() && path.str().starts_with(root) &&
      path.size() > root.size() && sys::path::is_separator(path[root.size()]))
    return path.substr(root.size() + 1).str();
  return path.str().str();
}

/// A debug location as an MLIR location body: "file":line:col, and when it
/// was inlined, callsite(<it> at <the call's location>), recursively (the
/// innermost position first).
static std::string sourceLoc(const DILocation *dl, StringRef root) {
  std::string here = quote(sourcePath(dl->getScope()->getFile(), root)) + ":" +
                     std::to_string(dl->getLine()) + ":" +
                     std::to_string(dl->getColumn());
  if (const DILocation *at = dl->getInlinedAt())
    return "callsite(" + here + " at " + sourceLoc(at, root) + ")";
  return here;
}

/// \p I's location: its source location (sourceLoc), inside a NameLoc with
/// \p I's name when \p named and the name is a source name (generatedName).
std::string Exporter::loc(const Instruction &I, bool named) {
  std::string child;
  if (const DILocation *dl = I.getDebugLoc().get())
    child = sourceLoc(dl, srcRoot);
  if (llvmLinks)
    child = "fused<" + quote(llvmLink(I)) + ">[" +
            (child.empty() ? kPosToken : child) + "]";
  if (named && I.hasName() && !generatedName(I)) {
    std::string n = quote(I.getName());
    return " loc(" + (child.empty() ? n : n + "(" + child + ")") + ")";
  }
  if (!child.empty())
    return " loc(" + child + ")";
  return "";
}

/// Whether a name is one SeaHorn generated, not a source name, so that a
/// location gets no NameLoc (it would show as `at_name=` in sea-mlir's
/// counterexamples): NameValues' `_N` (also with a suffix LLVM derives from
/// it, `_N.lcssa`), the shadow memory's versions (`sm<N>` calls and their
/// phis) and slots (`shadow.mem.<N>`).
static bool isGeneratedName(StringRef n) {
  if (n.starts_with("shadow.mem"))
    return true;
  StringRef base = n.split('.').first;
  return base.consume_front("_") && !base.empty() && all_of(base, isDigit);
}

bool Exporter::generatedName(const Value &v) const {
  return isMem(&v) || isGeneratedName(v.getName());
}

/// The function a call names, also when the call's type differs from the
/// declaration's (a C declaration without a prototype, `int nd();`, is
/// `declare i32 @nd(...)` called as `i32 ()`: getCalledFunction() is null).
/// Only the call site's types are used (CB.getType(), its arguments).
static const Function *calledFunction(const CallBase &CB) {
  return dyn_cast<Function>(CB.getCalledOperand()->stripPointerCasts());
}

void Exporter::findMemValues() {
  for (const Instruction &I : instructions(F))
    if (auto *cb = dyn_cast<CallBase>(&I))
      if (const Function *f = calledFunction(*cb))
        if (f->getName().starts_with("shadow.mem.") &&
            !cb->getType()->isVoidTy())
          memValues.insert(&I);
  // phis of versions, to a fixpoint
  bool changed = true;
  while (changed) {
    changed = false;
    for (const Instruction &I : instructions(F))
      if (auto *phi = dyn_cast<PHINode>(&I))
        if (!memValues.count(phi))
          for (const Value *in : phi->incoming_values())
            if (memValues.count(in)) {
              memValues.insert(phi);
              changed = true;
              break;
            }
  }
}

std::optional<std::string> Exporter::val(const Value *v,
                                         const Instruction &at) {
  auto it = names.find(v);
  if (it != names.end())
    return it->second;
  if (auto *c = dyn_cast<Constant>(v))
    return constant(c, at);
  error("operand has no definition yet", v);
  return std::nullopt;
}

std::optional<std::string> Exporter::constant(const Constant *c,
                                              const Instruction &at) {
  std::string l = loc(at, /*named=*/false); // the constant is not at's value
  if (auto *ci = dyn_cast<ConstantInt>(c))
    return emitConst(ci->getValue(), l);
  if (auto *cf = dyn_cast<ConstantFP>(c))
    return emitConst(cf->getValueAPF().bitcastToAPInt(), l); // its bits
  if (isa<ConstantPointerNull>(c)) {
    std::string n = fresh();
    os << "  " << n << " = sea.ptr.null : " << ptrTy << l << "\n";
    return n;
  }
  if (auto *gv = dyn_cast<GlobalVariable>(c)) {
    if (gv->hasInitializer() && !initializedGlobals.count(gv))
      droppedInit(*gv, initFailed.count(gv)
                           ? "it holds pointers or constant expressions"
                           : "its memory region has no "
                             "shadow.mem.global.init before this use");
    std::string n = fresh();
    uint64_t size = DL.getTypeAllocSize(gv->getValueType());
    // the global's declaration, when the debug info has it
    SmallVector<DIGlobalVariableExpression *, 1> dvs;
    gv->getDebugInfo(dvs);
    for (DIGlobalVariableExpression *e : dvs)
      if (const DIGlobalVariable *v = e->getVariable(); v && v->getLine()) {
        std::string pos = quote(sourcePath(v->getFile(), srcRoot)) + ":" +
                          std::to_string(v->getLine()) + ":0";
        if (llvmLinks) {
          std::string g;
          raw_string_ostream gs(g);
          gv->printAsOperand(gs, false, F.getParent());
          pos = "fused<" + quote("llvm " + g) + ">[" + pos + "]";
        }
        l = " loc(" + pos + ")";
        break;
      }
    os << "  " << n << " = sea.global @" << quote(gv->getName()) << " size "
       << size << " align " << objectAlign(gv->getPointerAlignment(DL), W / 8)
       << " : "
       << ptrTy << l << "\n";
    return n;
  }
  if (auto *fn = dyn_cast<Function>(c)) {
    std::string n = fresh();
    os << "  " << n << " = sea.func_addr @" << quote(fn->getName()) << " : "
       << ptrTy << l << "\n";
    return n;
  }
  if (auto *ce = dyn_cast<ConstantExpr>(c)) {
    if (ce->getOpcode() == Instruction::BitCast ||
        ce->getOpcode() == Instruction::AddrSpaceCast)
      return constant(ce->getOperand(0), at);
    if (auto *gep = dyn_cast<GEPOperator>(ce))
      return exportGep(*gep, at);
  }
  if (isa<StructType, ArrayType>(c->getType()))
    return aggregate(c, at);
  if (isa<FixedVectorType>(c->getType()))
    return vectorConstant(c, at);
  if (isa<UndefValue>(c) && c->getType()->isPointerTy()) {
    // an undef pointer: a value that can never be dereferenced
    std::string n = fresh();
    os << "  " << n << " = sea.ptr.nondet \"undef\" [" << site(&at) << "] : "
       << ptrTy << l << "\n";
    return n;
  }
  if (isa<UndefValue>(c) &&
      (c->getType()->isIntegerTy() || c->getType()->isFloatingPointTy())) {
    // sea has no undef: an explicit nondet value (as for aggregates)
    std::string n = fresh();
    os << "  " << n << " = sea.nondet \"undef\" [" << site(&at) << "] : "
       << *type(c->getType(), &at) << l << "\n";
    return n;
  }
  if (isa<UndefValue>(c)) {
    error("undef/poison operands are not supported", &at);
    return std::nullopt;
  }
  error("unsupported constant", c);
  return std::nullopt;
}

/// \p parts (value, width), lowest first, as one bit-vector (sea.concat).
std::string Exporter::concatParts(
    ArrayRef<std::pair<std::string, unsigned>> parts, const std::string &l) {
  std::string acc = parts[0].first;
  unsigned w = parts[0].second;
  for (auto [v, pw] : parts.drop_front()) {
    std::string r = fresh();
    os << "  " << r << " = sea.concat " << v << ", " << acc << " : i" << pw
       << ", i" << w << " -> i" << (w + pw) << l << "\n";
    acc = r;
    w += pw;
  }
  return acc;
}

/// A vector constant as one integer; undef / poison lanes are nondet bits
/// (sea has no undef: one explicit nondet of the vector's width; its undef
/// lanes are extracted and concatenated with the defined ones).
std::optional<std::string> Exporter::vectorConstant(const Constant *c,
                                                    const Instruction &at) {
  std::string l = loc(at, /*named=*/false); // the constant is not at's value
  auto *vt = cast<FixedVectorType>(c->getType());
  auto *et = dyn_cast<IntegerType>(vt->getElementType());
  if (!et) {
    error("vectors of non-integers are not supported", &at);
    return std::nullopt;
  }
  unsigned k = et->getBitWidth(), n = vt->getNumElements(), w = k * n;
  APInt bits(w, 0);
  SmallVector<bool> undef(n, false);
  for (unsigned i = 0; i < n; ++i) {
    const Constant *e = c->getAggregateElement(i);
    if (e && isa<UndefValue>(e)) {
      undef[i] = true;
      continue;
    }
    auto *ci = dyn_cast_or_null<ConstantInt>(e);
    if (!ci) {
      error("unsupported vector constant", c);
      return std::nullopt;
    }
    bits.insertBits(ci->getValue(), i * k);
  }
  if (llvm::none_of(undef, [](bool u) { return u; }))
    return emitConst(bits, l);
  std::string t = "i" + std::to_string(w), nd = fresh();
  os << "  " << nd << " = sea.nondet \"undef\" [" << site(&at) << "] : " << t
     << l << "\n";
  if (llvm::all_of(undef, [](bool u) { return u; }))
    return nd;
  // maximal runs of undef / defined lanes, lowest first
  SmallVector<std::pair<std::string, unsigned>> parts;
  for (unsigned i = 0; i < n;) {
    unsigned j = i;
    while (j < n && undef[j] == undef[i])
      ++j;
    unsigned lo = i * k, pw = (j - i) * k;
    if (undef[i]) {
      std::string r = fresh();
      os << "  " << r << " = sea.extract " << nd << "[" << lo << "] : " << t
         << " -> i" << pw << l << "\n";
      parts.push_back({r, pw});
    } else {
      parts.push_back({emitConst(bits.extractBits(pw, lo), l), pw});
    }
    i = j;
  }
  return concatParts(parts, l);
}

/// True if \p c is undef / poison somewhere (itself or a leaf).
static bool hasUndef(const Constant *c) {
  if (isa<UndefValue>(c))
    return true;
  if (!isa<StructType, ArrayType>(c->getType()))
    return false;
  for (unsigned i = 0, n = c->getNumOperands(); i < n; ++i)
    if (const Constant *f = c->getAggregateElement(i); f && hasUndef(f))
      return true;
  return false;
}

std::optional<std::string> Exporter::aggregate(const Constant *c,
                                               const Instruction &at) {
  std::string l = loc(at, /*named=*/false); // the constant is not at's value
  auto ty = type(c->getType(), &at);
  if (!ty)
    return std::nullopt;
  unsigned n = isa<StructType>(c->getType())
                   ? cast<StructType>(c->getType())->getNumElements()
                   : cast<ArrayType>(c->getType())->getNumElements();
  // sea has no undef: an aggregate that is undef (anywhere) starts as an
  // explicit nondet struct, and its defined fields are inserted into it.
  bool undef = hasUndef(c);
  std::string cur;
  if (undef) {
    cur = fresh();
    os << "  " << cur << " = sea.struct.nondet \"undef\" [" << site(&at)
       << "] : " << *ty << l << "\n";
    if (isa<UndefValue>(c))
      return cur;
  }
  std::vector<std::string> fields, types;
  for (unsigned i = 0; i < n; ++i) {
    const Constant *f = c->getAggregateElement(i);
    if (!f) {
      error("unsupported aggregate constant", c);
      return std::nullopt;
    }
    auto ft = type(f->getType(), &at);
    if (!ft)
      return std::nullopt;
    if (undef && isa<UndefValue>(f))
      continue; // stays nondet
    auto v = constant(f, at);
    if (!v)
      return std::nullopt;
    if (undef) {
      std::string r = fresh();
      os << "  " << r << " = sea.struct.insert " << *v << ", " << cur << "["
         << i << "] : " << *ft << " into " << *ty << l << "\n";
      cur = r;
      continue;
    }
    fields.push_back(*v);
    types.push_back(*ft);
  }
  if (undef)
    return cur;
  std::string r = fresh();
  os << "  " << r << " = sea.struct.create " << join(fields, ", ") << " : "
     << join(types, ", ") << " -> " << *ty << l << "\n";
  return r;
}

std::optional<std::string> Exporter::sizeVal(const Value *v,
                                             const Instruction &at) {
  auto n = val(v, at);
  if (!n)
    return std::nullopt;
  unsigned w = v->getType()->getIntegerBitWidth();
  if (w == W)
    return n;
  std::string r = fresh();
  os << "  " << r << " = sea." << (w < W ? "zext " : "trunc ") << *n << " : i"
     << w << " to i" << W << loc(at) << "\n";
  return r;
}

std::optional<std::pair<std::string, const Value *>>
Exporter::takeDef(const Instruction &I) {
  if (!pendingDef) {
    error("memory update without a shadow.mem.store before it", &I);
    return std::nullopt;
  }
  auto d = *pendingDef;
  pendingDef.reset();
  return d;
}

std::optional<std::string> Exporter::takeUse(const Instruction &I) {
  if (!pendingUse) {
    error("load without a shadow.mem.load before it", &I);
    return std::nullopt;
  }
  auto u = *pendingUse;
  pendingUse.reset();
  return u;
}

std::optional<std::string> Exporter::exportGep(const GEPOperator &gep,
                                               const Instruction &at) {
  // sea-mlir docs/design/PtrIndex.md: pointer arithmetic stays pointer
  // arithmetic. A GEP with a dynamic index of nonzero stride is one
  //   sea.ptr.index %base [%i..] strides [s..] offset c [inbounds]
  // (the op sign-extends narrow indices); a constant-only GEP is a
  // sea.ptr.add of its folded offset, as before.
  std::string l = loc(at);
  auto base = val(gep.getPointerOperand(), at);
  if (!base)
    return std::nullopt;
  // The folded constant (struct offsets, constant indices) is summed
  // exactly, in 2W bits: LLVM's inbounds promises no wrap of the partial
  // sums in GEP order, which does not make the out-of-order constant fit
  // (Fable's PtrIndex review, round 1, finding 6)
  APInt constOff(2 * W, 0);
  SmallVector<std::string> names, types;
  SmallVector<int64_t> strides;
  bool stridesFit = true;
  for (gep_type_iterator gti = gep_type_begin(gep), e = gep_type_end(gep);
       gti != e; ++gti) {
    const Value *idx = gti.getOperand();
    if (StructType *st = gti.getStructTypeOrNull()) {
      unsigned field = cast<ConstantInt>(idx)->getZExtValue();
      constOff += APInt(2 * W, DL.getStructLayout(st)->getElementOffset(field));
      continue;
    }
    uint64_t size = gti.getSequentialElementStride(DL).getFixedValue();
    if (auto *ci = dyn_cast<ConstantInt>(idx)) {
      // LangRef: the index is sign-extended or truncated to the index width
      constOff += APInt(2 * W, size) * ci->getValue().sextOrTrunc(W).sext(2 * W);
      continue;
    }
    if (!idx->getType()->isIntegerTy()) {
      error("vector GEP indices are not supported", &at);
      return std::nullopt;
    }
    // a zero-sized element type: the index contributes nothing (the op's
    // strides are nonzero)
    if (size == 0)
      continue;
    auto i = val(idx, at);
    if (!i)
      return std::nullopt;
    unsigned iw = idx->getType()->getIntegerBitWidth();
    std::string iW = *i;
    if (iw > W) {
      iW = fresh();
      os << "  " << iW << " = sea.trunc " << *i << " : i" << iw << " to i"
         << W << l << "\n";
      iw = W;
    }
    APInt s(W, size, /*isSigned=*/false);
    stridesFit &= APInt(128, size).isSignedIntN(W);
    names.push_back(iW);
    types.push_back("i" + std::to_string(iw));
    strides.push_back(W < 64 ? s.getSExtValue() : int64_t(s.getZExtValue()));
  }
  // a constant-only inbounds GEP keeps its promise (`&t->count`; PtrIndex.md
  // rev 7, A5): an index-free sea.ptr.index; without the flag, a ptr.add
  if (names.empty() && gep.isInBounds() && constOff.isSignedIntN(W) &&
      !constOff.isZero()) {
    std::string n = fresh();
    os << "  " << n << " = sea.ptr.index " << *base
       << " [] strides [] offset " << constOff.trunc(W).getSExtValue()
       << " inbounds : " << ptrTy << l << "\n";
    return n;
  }
  if (names.empty()) {
    if (constOff.isZero())
      return *base;
    // emitConst writes its own line: before this one
    std::string c = emitConst(constOff.trunc(W), l);
    std::string n = fresh();
    os << "  " << n << " = sea.ptr.add " << *base << ", " << c << " : "
       << ptrTy << ", i" << W << l << "\n";
    return n;
  }
  // inbounds only when its promise can be stated: the folded constant and
  // the strides are n-bit signed values
  bool inbounds = gep.isInBounds();
  if (inbounds && !(constOff.isSignedIntN(W) && stridesFit)) {
    warnOnce("gep-constant-overflow",
             "a GEP's folded constant or stride does not fit " + Twine(W) +
                 " signed bits: its inbounds is not exported "
                 "[export.gep-constant-overflow]");
    inbounds = false;
  }
  std::string n = fresh();
  os << "  " << n << " = sea.ptr.index " << *base << " [";
  for (size_t k = 0; k < names.size(); ++k)
    os << (k ? ", " : "") << names[k];
  os << "] strides [";
  for (size_t k = 0; k < strides.size(); ++k)
    os << (k ? ", " : "") << strides[k];
  os << "] offset " << constOff.trunc(W).getSExtValue()
     << (inbounds ? " inbounds" : "") << " : " << ptrTy;
  for (const std::string &t : types)
    os << ", " << t;
  os << l << "\n";
  return n;
}

void Exporter::exportShadow(const CallBase &CB, StringRef name) {
  std::string l = loc(CB);
  if (name == "shadow.mem.init" || name == "shadow.mem.arg.init") {
    // A region's initial contents: unconstrained.
    std::string n = fresh();
    os << "  " << n << " = sea.mem.nondet \"region." << regionOf(CB) << "\" ["
       << site(&CB) << "] : " << memTy << l << "\n";
    names[&CB] = n;
    return;
  }
  if (name == "shadow.mem.global.init") {
    // The region's version with the global's initializer stored; a global
    // whose initializer is not plain data starts uninitialized (warning).
    auto in = val(CB.getArgOperand(1), CB);
    if (!in)
      return;
    names[&CB] = *in;
    auto *gv = dyn_cast<GlobalVariable>(
        CB.getArgOperand(2)->stripPointerCastsAndAliases());
    if (!gv || !gv->hasInitializer())
      return;
    // initialized from here on (exportGlobalInit's own reference to gv
    // must not report its initializer as dropped)
    initializedGlobals.insert(gv);
    if (auto out = exportGlobalInit(*gv, *in, CB)) {
      names[&CB] = *out;
    } else {
      initializedGlobals.erase(gv);
      initFailed.insert(gv);
    }
    return;
  }
  if (name == "shadow.mem.store") {
    if (pendingDef)
      error("two shadow.mem.store without a memory update in between", &CB);
    auto in = val(CB.getArgOperand(1), CB);
    if (in)
      pendingDef = std::make_pair(*in, (const Value *)&CB);
    return;
  }
  if (name == "shadow.mem.load") {
    auto v = val(CB.getArgOperand(1), CB);
    if (v) {
      pendingUse = *v;
      pendingUseVersion = CB.getArgOperand(1);
    }
    return;
  }
  if (name == "shadow.mem.arg.ref") {
    // a region the next call reads: only sea_memdump has one
    // (SeaMlirPrepPass gave it a body)
    if (auto v = val(CB.getArgOperand(1), CB))
      pendingArgRefs.push_back(*v);
    return;
  }
  if (name == "shadow.mem.trsfr.load") {
    auto v = val(CB.getArgOperand(1), CB);
    if (v)
      pendingTrsfr = *v;
    return;
  }
  if (name == "shadow.mem.in" || name == "shadow.mem.out") {
    // What flows into / out of a function. In main, BvOpSem2 havocs it
    // (BvOpSem2.cc:1418-1431, a value of the call no instruction reads);
    // the region's version itself is unchanged.
    if (F.getName() != "main") {
      error(name + " outside main (functions are not exported yet)", &CB);
      return;
    }
    if (!CB.getType()->isVoidTy() && !CB.use_empty())
      error(name + " whose result is used is not supported", &CB);
    return;
  }
  error("unsupported shadow memory function " + name, &CB);
}

/// The bytes of \p c at \p off (little-endian); undef bytes stay unknown.
/// Returns false if \p c holds something that is not plain data (pointers,
/// constant expressions).
static bool initBytes(const Constant *c, uint64_t off, const DataLayout &DL,
                      SmallVectorImpl<std::optional<uint8_t>> &bytes) {
  if (isa<UndefValue>(c))
    return true;
  if (isa<ConstantAggregateZero>(c)) {
    for (uint64_t i = 0, n = DL.getTypeAllocSize(c->getType()); i < n; ++i)
      bytes[off + i] = 0;
    return true;
  }
  std::optional<APInt> bits;
  if (auto *ci = dyn_cast<ConstantInt>(c))
    bits = ci->getValue();
  else if (auto *cf = dyn_cast<ConstantFP>(c))
    bits = cf->getValueAPF().bitcastToAPInt();
  if (bits) {
    uint64_t n = DL.getTypeStoreSize(c->getType());
    APInt v = bits->zext(n * 8);
    for (uint64_t i = 0; i < n; ++i)
      bytes[off + i] = v.extractBitsAsZExtValue(8, 8 * i);
    return true;
  }
  if (auto *st = dyn_cast<StructType>(c->getType())) {
    const StructLayout *sl = DL.getStructLayout(st);
    for (unsigned i = 0; i < st->getNumElements(); ++i)
      if (!initBytes(c->getAggregateElement(i), off + sl->getElementOffset(i),
                     DL, bytes))
        return false;
    return true;
  }
  if (auto *at = dyn_cast<ArrayType>(c->getType())) {
    uint64_t stride = DL.getTypeAllocSize(at->getElementType());
    for (uint64_t i = 0; i < at->getNumElements(); ++i)
      if (!initBytes(c->getAggregateElement(i), off + i * stride, DL, bytes))
        return false;
    return true;
  }
  return false;
}

/// Whether every byte of \p c is one value, merged into \p b (unset: no
/// byte seen yet). False if \p c holds undef bytes, pointers or constant
/// expressions. Padding (struct padding, alloc size beyond store size) is
/// not looked at: a memset over the object also sets it, as the zero or
/// splat padding of the emitted object file.
static bool splatBytes(const Constant *c, const DataLayout &DL,
                       std::optional<uint8_t> &b) {
  auto merge = [&](uint8_t v) {
    if (!b)
      b = v;
    return *b == v;
  };
  if (isa<ConstantAggregateZero>(c))
    return DL.getTypeStoreSize(c->getType()) == 0 || merge(0);
  if (auto *cds = dyn_cast<ConstantDataSequential>(c)) {
    // the raw data (host order; a splat does not depend on it)
    for (char v : cds->getRawDataValues())
      if (!merge(static_cast<uint8_t>(v)))
        return false;
    return true;
  }
  std::optional<APInt> bits;
  if (auto *ci = dyn_cast<ConstantInt>(c))
    bits = ci->getValue();
  else if (auto *cf = dyn_cast<ConstantFP>(c))
    bits = cf->getValueAPF().bitcastToAPInt();
  if (bits) {
    uint64_t n = DL.getTypeStoreSize(c->getType());
    APInt v = bits->zext(n * 8);
    for (uint64_t i = 0; i < n; ++i)
      if (!merge(v.extractBitsAsZExtValue(8, 8 * i)))
        return false;
    return true;
  }
  if (isa<ConstantStruct, ConstantArray, ConstantVector>(c)) {
    for (unsigned i = 0, n = c->getNumOperands(); i < n; ++i)
      if (!splatBytes(cast<Constant>(c->getOperand(i)), DL, b))
        return false;
    return true;
  }
  return false; // undef, pointers, constant expressions
}

std::optional<std::string>
Exporter::exportGlobalInit(const GlobalVariable &gv, const std::string &mem,
                           const Instruction &at) {
  /// Above this many bytes, an initializer is left out (a store per byte).
  constexpr uint64_t kMaxInitBytes = 1 << 14;
  uint64_t size = DL.getTypeAllocSize(gv.getValueType());
  // All zero, or one repeated byte: one sea.memset over the object, at any
  // size (a 4 KiB zero array was 4096 stores).
  std::optional<uint8_t> splat;
  if (splatBytes(gv.getInitializer(), DL, splat)) {
    if (size == 0)
      return mem;
    std::string l = loc(at);
    auto base = constant(&gv, at);
    if (!base)
      return std::nullopt;
    std::string v = emitConst(APInt(8, splat.value_or(0)), l);
    std::string n = emitConst(APInt(W, size), l), r = fresh();
    os << "  " << r << " = sea.memset " << mem << "[" << *base << "], " << v
       << ", " << n << " inplace : " << memTy << l << "\n";
    return r;
  }
  if (!DL.isLittleEndian() || size > kMaxInitBytes) {
    droppedInit(gv, DL.isLittleEndian()
                        ? Twine(size) + " bytes, not one repeated byte, "
                              "larger than " + Twine(kMaxInitBytes)
                        : Twine("big-endian"));
    return std::nullopt;
  }
  SmallVector<std::optional<uint8_t>> bytes(size);
  if (!initBytes(gv.getInitializer(), 0, DL, bytes)) {
    droppedInit(gv, "it holds pointers or constant expressions");
    return std::nullopt;
  }
  std::string l = loc(at);
  auto base = constant(&gv, at);
  if (!base)
    return std::nullopt;
  std::string cur = mem;
  for (uint64_t i = 0; i < size; ++i) {
    if (!bytes[i])
      continue;
    std::string p = *base;
    if (i) {
      std::string o = emitConst(APInt(W, i), l);
      p = fresh();
      os << "  " << p << " = sea.ptr.add " << *base << ", " << o << " : "
         << ptrTy << ", i" << W << l << "\n";
    }
    std::string b = emitConst(APInt(8, *bytes[i]), l), r = fresh();
    os << "  " << r << " = sea.store " << cur << "[" << p << "], " << b
       << " inplace : " << memTy << ", i8" << l << "\n";
    cur = r;
  }
  return cur;
}

void Exporter::exportInlineAsm(const CallBase &CB, const InlineAsm &IA) {
  // Only the patterns BvOpSem2 handles (visitInlineAsmCall): an empty body
  // that copies its input or only uses it (optimization barriers), a body
  // of only assembler comments with memory / flags clobbers (a compiler
  // barrier, isInlineAsmBarrier), and a single byte swap.
  std::string l = loc(CB);
  StringRef body = StringRef(IA.getAsmString()).trim();
  StringRef cons = IA.getConstraintString();
  auto *ty = dyn_cast<IntegerType>(CB.getType());
  if (body.empty() && CB.arg_size() == 1 && cons.starts_with("=r,0,")) {
    if (auto a = val(CB.getArgOperand(0), CB))
      names[&CB] = *a;
    return;
  }
  if ((body.empty() && CB.getType()->isVoidTy() && cons.starts_with("r,")) ||
      isInlineAsmBarrier(CB, IA)) {
    if (cons.contains("~{memory}"))
      warnOnce("asm-barrier",
               "inline assembly with an empty or comment-only body and a "
               "memory clobber treated as a no-op (as BvOpSem2)");
    return;
  }
  bool isBswap =
      body == "bswap $0" || body == "bswapl $0" || body == "bswapq $0" ||
      body == "bswap ${0:q}" || body == "bswapl ${0:q}" ||
      body == "bswapq ${0:q}" ||
      (ty && ty->getBitWidth() == 16 && cons.starts_with("=r,0,") &&
       (body == "rorw $$8, ${0:w}" || body == "rolw $$8, ${0:w}"));
  if (isBswap && ty && ty->getBitWidth() % 16 == 0 && CB.arg_size() == 1) {
    auto a = val(CB.getArgOperand(0), CB);
    if (!a)
      return;
    std::string n = fresh();
    os << "  " << n << " = sea.bswap " << *a << " : i" << ty->getBitWidth()
       << l << "\n";
    names[&CB] = n;
    return;
  }
  error("unsupported inline assembly \"" + IA.getAsmString() + "\" (\"" +
            cons + "\")",
        &CB);
}

void Exporter::exportBitIntrinsic(const CallBase &CB, Intrinsic::ID id) {
  std::string l = loc(CB);
  auto *it = dyn_cast<IntegerType>(CB.getType());
  if (!it) {
    error("vector intrinsics are not supported", &CB);
    return;
  }
  auto x = val(CB.getArgOperand(0), CB);
  if (!x)
    return;
  unsigned w = it->getBitWidth();
  std::string ty = "i" + std::to_string(w);
  auto op = [&](StringRef o, const std::string &a, const std::string &b,
                const std::string &t) {
    std::string r = fresh();
    os << "  " << r << " = sea." << o << " " << a << ", " << b << " : " << t
       << l << "\n";
    return r;
  };
  auto select = [&](const std::string &c, const std::string &a,
                    const std::string &b, const std::string &t) {
    std::string r = fresh();
    os << "  " << r << " = sea.select " << c << ", " << a << ", " << b << " : "
       << t << l << "\n";
    return r;
  };
  if (id == Intrinsic::bitreverse) {
    // bit i of the result is bit w-1-i of x: the w one-bit extracts,
    // lowest result bit (x's top bit) first, concatenated
    if (w == 1) {
      names[&CB] = *x;
      return;
    }
    SmallVector<std::pair<std::string, unsigned>> parts;
    for (unsigned i = 0; i < w; ++i) {
      std::string r = fresh();
      os << "  " << r << " = sea.extract " << *x << "[" << (w - 1 - i)
         << "] : " << ty << " -> i1" << l << "\n";
      parts.push_back({r, 1});
    }
    names[&CB] = concatParts(parts, l);
    return;
  }
  // cttz / ctlz: binary search on x zero-extended to a power-of-two width
  // P (the extra high bits are zero: they do not change cttz and add P - w
  // to ctlz). Step k = P/2, ..., 1: if the low (cttz) / high (ctlz) k bits
  // of the current value are zero, count k and shift them out. A zero input
  // is w, also with is_zero_poison (sea has no poison; LLVM's value with
  // is_zero_poison = false).
  bool trailing = id == Intrinsic::cttz;
  unsigned P = PowerOf2Ceil(w);
  std::string pty = "i" + std::to_string(P);
  std::string cur = *x;
  if (P != w) {
    cur = fresh();
    os << "  " << cur << " = sea.zext " << *x << " : " << ty << " to " << pty
       << l << "\n";
  }
  std::string zero = emitConst(APInt::getZero(P), l);
  std::string n = zero;
  for (unsigned k = P / 2; k >= 1; k /= 2) {
    // trailing: cur & (2^k - 1) == 0; leading: cur >> (P - k) == 0
    std::string part =
        trailing ? op("and", cur, emitConst(APInt::getLowBitsSet(P, k), l), pty)
                 : op("lshr", cur, emitConst(APInt(P, P - k), l), pty);
    std::string none = fresh();
    os << "  " << none << " = sea.icmp eq, " << part << ", " << zero << " : "
       << pty << l << "\n";
    std::string kc = emitConst(APInt(P, k), l);
    n = select(none, op("add", n, kc, pty), n, pty);
    cur = select(none, op(trailing ? "lshr" : "shl", cur, kc, pty), cur, pty);
  }
  // n counts the zeros below / above the first set bit of a non-zero input
  if (!trailing && P != w)
    n = op("sub", n, emitConst(APInt(P, P - w), l), pty);
  if (P != w) {
    std::string t = fresh();
    os << "  " << t << " = sea.trunc " << n << " : " << pty << " to " << ty
       << l << "\n";
    n = t;
  }
  std::string zw = emitConst(APInt::getZero(w), l), isZero = fresh();
  os << "  " << isZero << " = sea.icmp eq, " << *x << ", " << zw << " : "
     << ty << l << "\n";
  std::string wc = emitConst(APInt(w, w), l);
  names[&CB] = select(isZero, wc, n, ty);
}

bool Exporter::exportIntrinsic(const CallBase &CB, Intrinsic::ID id) {
  std::string l = loc(CB);
  auto emit = [&](const std::string &op, unsigned nargs, Type *t) {
    std::vector<std::string> args;
    for (unsigned i = 0; i < nargs; ++i) {
      auto a = val(CB.getArgOperand(i), CB);
      if (!a)
        return std::optional<std::string>();
      args.push_back(*a);
    }
    std::string n = fresh();
    os << "  " << n << " = sea." << op << " " << join(args, ", ") << " : "
       << *type(t, &CB) << l << "\n";
    return std::optional<std::string>(n);
  };
  const char *op = nullptr;
  unsigned nargs = 2;
  switch (id) {
  case Intrinsic::umin: op = "umin"; break;
  case Intrinsic::umax: op = "umax"; break;
  case Intrinsic::smin: op = "smin"; break;
  case Intrinsic::smax: op = "smax"; break;
  case Intrinsic::bswap: op = "bswap"; nargs = 1; break;
  case Intrinsic::ctpop: op = "ctpop"; nargs = 1; break;
  case Intrinsic::fshl: op = "fshl"; nargs = 3; break;
  case Intrinsic::fshr: op = "fshr"; nargs = 3; break;
  case Intrinsic::cttz:
  case Intrinsic::ctlz:
  case Intrinsic::bitreverse:
    exportBitIntrinsic(CB, id);
    return true;
  case Intrinsic::expect:
    if (auto a = val(CB.getArgOperand(0), CB))
      names[&CB] = *a;
    return true;
  case Intrinsic::experimental_noalias_scope_decl:
    return true; // an optimizer hint: no effect on values
  case Intrinsic::assume:
    // false is undefined behaviour: the execution is infeasible
    if (auto c = val(CB.getArgOperand(0), CB))
      os << "  sea.assume " << *c << l << "\n";
    return true;
  case Intrinsic::uadd_sat:
  case Intrinsic::usub_sat:
  case Intrinsic::sadd_sat:
  case Intrinsic::ssub_sat: {
    // saturating: the plain result unless it overflows, then the bound
    // (LangRef): unsigned 2^w-1 / 0; signed by the first operand's sign
    Type *t = CB.getType();
    if (!t->isIntegerTy()) {
      error("vector intrinsics are not supported", &CB);
      return true;
    }
    bool add = id == Intrinsic::uadd_sat || id == Intrinsic::sadd_sat;
    bool sgn = id == Intrinsic::sadd_sat || id == Intrinsic::ssub_sat;
    unsigned w = t->getIntegerBitWidth();
    std::string ty = *type(t, &CB);
    auto v = emit(add ? "add" : "sub", 2, t);
    auto o = emit(sgn ? (add ? "saddo" : "ssubo") : (add ? "uaddo" : "usubo"),
                  2, t);
    auto a = val(CB.getArgOperand(0), CB);
    if (!v || !o || !a)
      return true;
    std::string bound;
    if (!sgn) {
      bound = emitConst(add ? APInt::getAllOnes(w) : APInt::getZero(w), l);
    } else {
      std::string z = emitConst(APInt::getZero(w), l), neg = fresh();
      os << "  " << neg << " = sea.icmp slt, " << *a << ", " << z << " : "
         << ty << l << "\n";
      std::string mn = emitConst(APInt::getSignedMinValue(w), l),
                  mx = emitConst(APInt::getSignedMaxValue(w), l);
      bound = fresh();
      os << "  " << bound << " = sea.select " << neg << ", " << mn << ", " << mx
         << " : " << ty << l << "\n";
    }
    std::string r = fresh();
    os << "  " << r << " = sea.select " << *o << ", " << bound << ", " << *v
       << " : " << ty << l << "\n";
    names[&CB] = r;
    return true;
  }
  default:
    break;
  }
  if (op) {
    if (!CB.getType()->isIntegerTy()) {
      error("vector intrinsics are not supported", &CB);
      return true;
    }
    if (auto n = emit(op, nargs, CB.getType()))
      names[&CB] = *n;
    return true;
  }
  // {iN, i1} = llvm.*.with.overflow: the value is the plain op, the
  // overflow bit an overflow op (sea.uaddo, ...); extractvalue picks one.
  const char *arith = nullptr;
  switch (id) {
  case Intrinsic::uadd_with_overflow: arith = "add"; op = "uaddo"; break;
  case Intrinsic::sadd_with_overflow: arith = "add"; op = "saddo"; break;
  case Intrinsic::usub_with_overflow: arith = "sub"; op = "usubo"; break;
  case Intrinsic::ssub_with_overflow: arith = "sub"; op = "ssubo"; break;
  case Intrinsic::umul_with_overflow: arith = "mul"; op = "umulo"; break;
  case Intrinsic::smul_with_overflow: arith = "mul"; op = "smulo"; break;
  default:
    return false;
  }
  Type *t = CB.getArgOperand(0)->getType();
  if (!t->isIntegerTy()) {
    error("vector intrinsics are not supported", &CB);
    return true;
  }
  auto v = emit(arith, 2, t), o = emit(op, 2, t);
  if (v && o)
    overflowParts[&CB] = {*v, *o};
  return true;
}

void Exporter::exportCall(const CallBase &CB) {
  const Function *f = calledFunction(CB);
  if (!f) {
    if (auto *ia = dyn_cast<InlineAsm>(CB.getCalledOperand())) {
      exportInlineAsm(CB, *ia);
      return;
    }
    // An indirect call SeaHorn's devirtualization left: an unknown function,
    // as BvOpSem2 treats it (no effect, nondet result); one that defines
    // memory is not supported.
    if (pendingDef) {
      error("indirect call that defines memory; not supported", &CB);
      return;
    }
    pendingUse.reset();
    if (CB.getType()->isVoidTy() || CB.use_empty()) {
      warnOnce("indirect", "indirect call treated as a no-op");
      return;
    }
    warnOnce("indirect", "indirect call treated as a no-op returning a "
                         "nondet value");
    auto t = type(CB.getType(), &CB);
    if (!t)
      return;
    if (CB.getType()->isPointerTy()) {
      std::string n = fresh();
      os << "  " << n << " = sea.ptr.nondet \"indirect\" [" << site(&CB)
         << "] : " << ptrTy << loc(CB) << "\n";
      names[&CB] = n;
      return;
    }
    std::string n = fresh();
    os << "  " << n << " = sea.nondet \"indirect\" [" << site(&CB) << "] : "
       << *t << loc(CB) << "\n";
    names[&CB] = n;
    return;
  }
  StringRef name = f->getName();
  std::string l = loc(CB);
  if (name.starts_with("shadow.mem."))
    return exportShadow(CB, name);
  if (name == "seahorn.fn.enter" || name == "seahorn.fail" ||
      name == "verifier.error" || name.starts_with("llvm.lifetime.") ||
      name.starts_with("llvm.dbg."))
    return; // no effect on the VC (the error path ends at the return)
  // Modification tracking: markers (sea-apply-tracking makes the updates
  // between them `tracked`); queries and resets name their memory version
  // (from the shadow.mem.load / shadow.mem.store before them).
  if (name == "sea.tracking_on" || name == "sea.tracking_off") {
    os << "  sea." << name.drop_front(4) << l << "\n";
    return;
  }
  if (name == "sea.is_modified") {
    auto m = takeUse(CB);
    auto p = val(CB.getArgOperand(0), CB);
    if (!m || !p)
      return;
    if (!CB.getType()->isIntegerTy(1)) {
      error("sea.is_modified must return i1", &CB);
      return;
    }
    std::string r = fresh();
    os << "  " << r << " = sea.mem.is_modified " << *m << "[" << *p
       << "] : " << memTy << l << "\n";
    names[&CB] = r;
    return;
  }
  if (name == "sea.reset_modified") {
    auto d = takeDef(CB);
    auto p = val(CB.getArgOperand(0), CB);
    if (!d || !p)
      return;
    std::string r = fresh();
    os << "  " << r << " = sea.mem.reset_modified " << d->first << "[" << *p
       << "] inplace : " << memTy << l << "\n";
    names[d->second] = r;
    return;
  }
  if (name == "memhavoc") {
    // SeaHorn's ShadowMem gives memhavoc a memory use, not a definition
    // (sea-dsa ShadowMem.cc visitMemhavoc), so mono does not havoc. Export
    // the havoc as a new version (sea.memhavoc) and let later uses of the
    // version see it; sea-drop-fresh-memhavoc removes the ones on a fresh
    // allocation, where they are no-ops. Safe only if every other use of
    // the version comes after the memhavoc.
    if (!pendingUse) {
      // no memory region (sea-dsa found no cell for the pointer): no load
      // reads this memory, so there is nothing to havoc
      warnOnce("memhavoc-no-region",
               "memhavoc of memory in no region: nothing reads it (no-op)");
      return;
    }
    const Value *ver = pendingUseVersion;
    std::string m = *pendingUse;
    pendingUse.reset();
    pendingUseVersion = nullptr;
    DominatorTree dt(const_cast<Function &>(F));
    for (const Use &u : ver->uses()) {
      auto *ui = dyn_cast<Instruction>(u.getUser());
      if (!ui || ui->getNextNode() == &CB)
        continue; // its own shadow.mem.load
      if (!dt.dominates(&CB, u)) { // a phi's use is at its incoming edge
        error("memhavoc: a use of the memory version it havocs is not after "
              "it (cannot give it a new version)",
              &CB);
        return;
      }
    }
    auto p = val(CB.getArgOperand(0), CB), n = sizeVal(CB.getArgOperand(1), CB);
    if (!p || !n)
      return;
    std::string r = fresh();
    os << "  " << r << " = sea.memhavoc " << m << "[" << *p << "], " << *n
       << " [" << site(&CB) << "] inplace : " << memTy << l << "\n";
    names[ver] = r;
    return;
  }
  if (name == "sea.is_dereferenceable") {
    // the bounds check's assertion (or a harness's): [p, p+n) in p's object
    if (!CB.getType()->isIntegerTy(1)) {
      error("sea.is_dereferenceable must return i1", &CB);
      return;
    }
    auto p = val(CB.getArgOperand(0), CB), n = sizeVal(CB.getArgOperand(1), CB);
    if (!p || !n)
      return;
    std::string r = fresh();
    os << "  " << r << " = sea.ptr.dereferenceable " << *p << ", " << *n
       << " : " << ptrTy << ", i" << W << l << "\n";
    names[&CB] = r;
    return;
  }
  if (name == "verifier.assume" || name == "verifier.assume.not") {
    auto c = val(CB.getArgOperand(0), CB);
    if (!c)
      return;
    std::string cond = *c;
    if (name == "verifier.assume.not") {
      std::string t = fresh(), n = fresh();
      os << "  " << t << " = sea.const 1 : i1" << l << "\n";
      os << "  " << n << " = sea.xor " << *c << ", " << t << " : i1" << l
         << "\n";
      cond = n;
    }
    os << "  sea.assume " << cond << l << "\n";
    return;
  }
  if (name == "sea_printf")
    return exportPrintf(CB, l);
  if (name == "sea_memdump")
    return exportMemdump(CB, l);
  if (!pendingArgRefs.empty()) {
    error("shadow.mem.arg.ref before a call that is not sea_memdump", &CB);
    return;
  }
  if (f->isDeclaration() && CB.arg_empty() && !CB.getType()->isVoidTy() &&
      (name.starts_with("nd") || name.starts_with("nondet") ||
       name.starts_with("verifier.nondet") ||
       name.starts_with("__VERIFIER_nondet"))) {
    if (CB.getType()->isPointerTy()) {
      // a pointer value that can never be dereferenced (harnesses mark
      // fields that must not be dereferenced with it)
      std::string n = fresh();
      os << "  " << n << " = sea.ptr.nondet " << quote(name) << " ["
         << site(&CB) << "] : " << ptrTy << l << "\n";
      names[&CB] = n;
      return;
    }
    if (!CB.getType()->isIntegerTy()) {
      error("nondet values of non-integer type are not supported", &CB);
      return;
    }
    std::string n = fresh();
    os << "  " << n << " = sea.nondet " << quote(name) << " [" << site(&CB)
       << "] : " << *type(CB.getType(), &CB) << l << "\n";
    names[&CB] = n;
    return;
  }
  // LLVM's alignment promise, in bytes (sea `align`; 1 says nothing).
  auto align = [](MaybeAlign a, const char *kw = " align ") -> std::string {
    if (!a || a->value() == 1)
      return "";
    return kw + std::to_string(a->value());
  };
  // A memory intrinsic on memory in no region (sea-dsa found no cell: no
  // shadow store / load is attached): nothing reads that memory, so it is a
  // no-op (as a region-less memhavoc).
  if (isa<MemSetInst, MemTransferInst>(&CB) && !pendingDef && !pendingTrsfr &&
      !pendingUse) {
    warnOnce("memop-no-region",
             "memset/memcpy/memmove of memory in no region: nothing reads it "
             "(no-op)");
    return;
  }
  if (auto *ms = dyn_cast<MemSetInst>(&CB)) {
    auto d = takeDef(CB);
    auto p = val(ms->getDest(), CB), v = val(ms->getValue(), CB),
         n = sizeVal(ms->getLength(), CB);
    if (!d || !p || !v || !n)
      return;
    std::string r = fresh();
    os << "  " << r << " = sea.memset " << d->first << "[" << *p << "], " << *v
       << ", " << *n << " inplace" << align(ms->getDestAlign()) << " : "
       << memTy << l << "\n";
    names[d->second] = r;
    return;
  }
  if (auto *mt = dyn_cast<MemTransferInst>(&CB)) {
    auto d = takeDef(CB);
    if (!pendingTrsfr) {
      error("memcpy/memmove without a shadow.mem.trsfr.load before it", &CB);
      return;
    }
    std::string src = *pendingTrsfr;
    pendingTrsfr.reset();
    auto dp = val(mt->getDest(), CB), sp = val(mt->getSource(), CB),
         n = sizeVal(mt->getLength(), CB);
    if (!d || !dp || !sp || !n)
      return;
    // memcpy and memmove mean the same in sea (a new version); memcpy's
    // disjointness precondition is a sea-mlir pass.
    std::string r = fresh();
    os << "  " << r << " = sea.memmove " << d->first << "[" << *dp << "], "
       << src << "[" << *sp << "], " << *n << " inplace"
       << align(mt->getDestAlign())
       << align(mt->getSourceAlign(), " src_align ") << " : " << memTy << l
       << "\n";
    names[d->second] = r;
    return;
  }
  if (name == "malloc" || name == "calloc") {
    // Allocation is a definition (--horn-shadow-mem-alloc-is-def).
    std::optional<std::string> size;
    if (name == "malloc") {
      size = sizeVal(CB.getArgOperand(0), CB);
    } else {
      auto a = sizeVal(CB.getArgOperand(0), CB),
           b = sizeVal(CB.getArgOperand(1), CB);
      if (a && b) {
        size = fresh();
        os << "  " << *size << " = sea.mul " << *a << ", " << *b << " : i" << W
           << l << "\n";
      }
    }
    if (!size)
      return;
    std::string p = fresh();
    os << "  " << p << " = sea.malloc " << *size << " align 16 [" << site(&CB)
       << "] : i" << W << " -> " << ptrTy << l << "\n";
    names[&CB] = p;
    if (pendingDef) {
      auto d = *takeDef(CB);
      if (name == "calloc") {
        std::string z = emitConst(APInt(8, 0), l), r = fresh();
        os << "  " << r << " = sea.memset " << d.first << "[" << p << "], " << z
           << ", " << *size << " inplace : " << memTy << l << "\n";
        names[d.second] = r;
      } else {
        names[d.second] = d.first;
      }
    } else if (name == "calloc") {
      error("calloc without a shadow.mem.store before it", &CB);
    }
    return;
  }
  if (name == "free") {
    auto p = val(CB.getArgOperand(0), CB);
    if (p)
      os << "  sea.free " << *p << " : " << ptrTy << l << "\n";
    if (pendingDef) {
      auto d = *takeDef(CB);
      names[d.second] = d.first;
    }
    return;
  }
  if (name.starts_with("smt.concat.") || name.starts_with("smt.extract.")) {
    error("smt.concat / smt.extract are not exported yet", &CB);
    return;
  }
  if (f->isIntrinsic()) {
    if (!exportIntrinsic(CB, f->getIntrinsicID()))
      error("unsupported intrinsic " + name + " (add a sea op for it)", &CB);
    return;
  }
  if (!f->isDeclaration()) {
    error("call to defined function " + name +
              " (the exporter expects it inlined)",
          &CB);
    return;
  }
  // An external function: no effect, nondet result (as BvOpSem2).
  if (pendingDef) {
    error("call to " + name + " defines memory; not supported", &CB);
    return;
  }
  if (CB.getType()->isVoidTy() || CB.use_empty()) {
    warnOnce("ext:" + name,
             "call to external function " + name + " treated as a no-op");
    return;
  }
  warnOnce("ext:" + name, "call to external function " + name +
                              " treated as a no-op returning a nondet value");
  if (!CB.getType()->isIntegerTy() && !CB.getType()->isFloatingPointTy()) {
    error("external call returning a non-integer is not supported", &CB);
    return;
  }
  std::string n = fresh();
  os << "  " << n << " = sea.nondet " << quote(name) << " [" << site(&CB)
     << "] : " << *type(CB.getType(), &CB) << l << "\n";
  names[&CB] = n;
}

/// One conversion of a printf format: its letter and the label the literal
/// text before it (since the previous conversion) gives.
struct PrintfConv {
  char conv;
  std::string label;
};

/// The label in the text before a conversion: its trailing identifier-like
/// token (`[A-Za-z_][A-Za-z0-9_.\[\]]*`), after the spaces and separators
/// that end it (`=`, `:`, `,`, `;`, `(`): "x=%d" and " inc=%u" give "x" and
/// "inc", "pre: stream=%p" gives "stream"; "" when there is none. \p lead
/// gets the text before the token.
static std::string printfLabel(StringRef text, StringRef *lead = nullptr) {
  auto isTok = [](char c) {
    return isAlnum(c) || StringRef("_.[]").contains(c);
  };
  StringRef t = text.rtrim(" \t\r\n=:,;(");
  size_t b = t.size();
  while (b > 0 && isTok(t[b - 1]))
    --b;
  // the token starts at a letter or `_` ("0x%x" gives "x")
  while (b < t.size() && !isAlpha(t[b]) && t[b] != '_')
    ++b;
  if (lead)
    *lead = t.take_front(b);
  return t.drop_front(b).str();
}

/// The leading text of a format (before its first label) as a print scope
/// tag: its words (runs of letters, digits, `_`) from the first that starts
/// with a letter or `_`, joined by `_` ("pre: " gives "pre", "after step 2: "
/// gives "after_step_2"); "" when it has no identifier ("--> ", "1: ").
static std::string printfScope(StringRef lead) {
  std::string tag;
  while (!lead.empty()) {
    lead = lead.drop_while([](char c) { return !isAlnum(c) && c != '_'; });
    StringRef w =
        lead.take_while([](char c) { return isAlnum(c) || c == '_'; });
    lead = lead.drop_front(w.size());
    if (w.empty() || (tag.empty() && isDigit(w[0])))
      continue;
    tag += (tag.empty() ? "" : "_") + w.str();
  }
  return tag;
}

/// The conversions of \p fmt, or false for what the minimal parser does not
/// know (`*` width or precision, %n, an unknown conversion): flags, width,
/// precision and length modifiers are skipped; "%%" is a literal %. \p scope
/// gets the scope tag of the text before the first conversion's label.
static bool parsePrintf(StringRef fmt, SmallVectorImpl<PrintfConv> &convs,
                        std::string &scope) {
  std::string text;
  for (size_t i = 0; i < fmt.size(); ++i) {
    if (fmt[i] != '%') {
      text += fmt[i];
      continue;
    }
    if (++i < fmt.size() && fmt[i] == '%') {
      text += '%';
      continue;
    }
    while (i < fmt.size() && StringRef("-+ #0'").contains(fmt[i]))
      ++i;
    while (i < fmt.size() && isDigit(fmt[i]))
      ++i;
    if (i < fmt.size() && fmt[i] == '.')
      for (++i; i < fmt.size() && isDigit(fmt[i]);)
        ++i;
    while (i < fmt.size() && StringRef("hljztLq").contains(fmt[i]))
      ++i;
    if (i == fmt.size() || !StringRef("diouxXcspfFeEgGaA").contains(fmt[i]))
      return false;
    StringRef lead;
    convs.push_back({fmt[i], printfLabel(text, &lead)});
    if (convs.size() == 1)
      scope = printfScope(lead);
    text.clear();
  }
  return true;
}

/// sea_printf(fmt, ...) (SeaHorn's counterexample printf; BmcImpl prints
/// its named arguments) as sea-mlir prints (docs/design/Print.md), which
/// encode nothing in the VC:
/// - each integer or pointer argument: one strong sea.print. Label: the
///   trailing identifier of the format's text before its conversion
///   ("pre: x=%d" -> "x"), else the debug variable the argument holds, else
///   its LLVM name (not one SeaHorn generated), else arg<k>. Format (when the
///   format string is a constant the minimal parser reads and its conversions
///   match the arguments): %d %i -> s, %u -> u, %x %X -> x, %c -> c, %s %p of
///   an integer -> x, else auto; pointers always print as pointers (object +
///   offset);
/// - a constant string argument (%s of a literal): a tag line
///   `label = "text"`; another constant pointer that is not null: a tag
///   line naming its global;
/// - the format's leading text before the first label, if it has an
///   identifier: a print scope around the call's prints ("pre: x=%d" ->
///   sea.print.scope "pre", the path pre.x);
/// - a call without arguments: a tag line with the format (else
///   "sea_printf");
/// - other arguments (floats, aggregates, vectors): a warning, not printed.
void Exporter::exportPrintf(const CallBase &CB, const std::string &l) {
  // A memory use or definition SeaHorn's shadow memory may attach to the
  // call (the declaration is normally noalias): prints change no memory.
  pendingUse.reset();
  pendingUseVersion = nullptr;
  if (pendingDef) {
    auto d = *takeDef(CB);
    names[d.second] = d.first;
  }
  std::string where;
  if (const DebugLoc &dl = CB.getDebugLoc())
    where = " at line " + std::to_string(dl.getLine());
  StringRef fmt;
  bool haveFmt =
      CB.arg_size() > 0 && getConstantStringInfo(CB.getArgOperand(0), fmt);
  SmallVector<PrintfConv> convs;
  std::string scope;
  unsigned nargs = CB.arg_size() > 0 ? CB.arg_size() - 1 : 0;
  bool matched =
      haveFmt && parsePrintf(fmt, convs, scope) && convs.size() == nargs;
  if (nargs == 0) {
    // one output line: the format's line breaks become spaces
    std::string tag = haveFmt ? fmt.trim().str() : "";
    std::replace(tag.begin(), tag.end(), '\n', ' ');
    os << "  sea.print " << quote(tag.empty() ? "sea_printf" : tag) << l
       << "\n";
    return;
  }
  if (!haveFmt)
    WARN << "sea-mlir export: sea_printf" << where
         << ": the format is not a constant string; its arguments are "
            "printed with positional labels and fmt auto";
  else if (!matched)
    WARN << "sea-mlir export: sea_printf" << where
         << ": cannot match the format " << quote(fmt) << " to its " << nargs
         << " arguments; they are printed with positional labels and fmt "
            "auto";
  if (!matched)
    scope.clear();
  if (!scope.empty())
    os << "  sea.print.scope " << quote(scope) << l << "\n";
  for (unsigned k = 0; k < nargs; ++k) {
    const Value *a = CB.getArgOperand(k + 1);
    std::string label = matched ? convs[k].label : "";
    // the variable an llvm.dbg.value says the argument holds
    if (auto *md = LocalAsMetadata::getIfExists(const_cast<Value *>(a));
        md && label.empty())
      if (auto *mv = MetadataAsValue::getIfExists(a->getContext(), md))
        for (const User *u : mv->users())
          if (auto *dv = dyn_cast<DbgValueInst>(u);
              dv && dv->getVariable() &&
              !dv->getVariable()->getName().empty()) {
            label = dv->getVariable()->getName().str();
            break;
          }
    if (label.empty() && a->hasName() && !generatedName(*a))
      label = a->getName().str();
    if (label.empty())
      label = "arg" + std::to_string(k + 1);
    Type *t = a->getType();
    if (t->isPointerTy() && isa<Constant>(a) && !isa<ConstantPointerNull>(a)) {
      StringRef str;
      if (getConstantStringInfo(a, str)) {
        os << "  sea.print " << quote(label + " = \"" + str.str() + "\"") << l
           << "\n";
        continue;
      }
      int64_t off = 0;
      const Value *base = GetPointerBaseWithConstantOffset(a, off, DL);
      std::string tok = isa<GlobalValue>(base)
                            ? "&global." + base->getName().str() + "[" +
                                  std::to_string(off) + "]"
                            : "a constant pointer";
      os << "  sea.print " << quote(label + " = " + tok) << l << "\n";
      continue;
    }
    if (!t->isIntegerTy() && !t->isPointerTy()) {
      std::string ts;
      raw_string_ostream tos(ts);
      tos << *t;
      WARN << "sea-mlir export: sea_printf" << where << ": argument " << k + 1
           << " (" << label << ") of type " << ts
           << " is not printed (only integers and pointers are)";
      continue;
    }
    auto v = val(a, CB);
    auto ty = type(t, &CB);
    if (!v || !ty)
      return;
    const char *f = nullptr;
    if (matched && t->isIntegerTy()) {
      switch (convs[k].conv) {
      case 'd':
      case 'i':
        f = "s";
        break;
      case 'u':
        f = "u";
        break;
      case 'x':
      case 'X':
      case 'p':
      case 's':
        f = "x";
        break;
      case 'c':
        f = "c";
        break;
      default:
        break;
      }
    }
    os << "  sea.print " << quote(label) << " " << *v << " : " << *ty;
    if (f)
      os << " {fmt = \"" << f << "\"}";
    os << l << "\n";
  }
  if (!scope.empty())
    os << "  sea.print.end " << quote(scope) << l << "\n";
}

/// sea_memdump(label, p, n) (seahorn.h) as a strong hex dump of n bytes at p
/// in the memory version current at the call, which the shadow memory
/// passes it (shadow.mem.arg.ref, SeaMlirPrepPass):
///   sea.print.mem "label" %m[%p], %n : !sea.mem<...>, iN -> i8
///       {fmt = "hexdump"}
/// The label is the constant string (else "sea_memdump" and a warning);
/// sea-mlir caps the count at 65536. Without a region (p has no shadow
/// memory) nothing is printed (a warning). Prints encode nothing in the VC.
void Exporter::exportMemdump(const CallBase &CB, const std::string &l) {
  SmallVector<std::string, 1> refs = std::move(pendingArgRefs);
  pendingArgRefs.clear();
  pendingUse.reset();
  pendingUseVersion = nullptr;
  if (pendingDef) {
    error("sea_memdump defines memory; not supported", &CB);
    return;
  }
  std::string where;
  if (const DebugLoc &dl = CB.getDebugLoc())
    where = " at line " + std::to_string(dl.getLine());
  if (CB.arg_size() != 3 || !CB.getArgOperand(1)->getType()->isPointerTy() ||
      !CB.getArgOperand(2)->getType()->isIntegerTy()) {
    error("sea_memdump(const char *label, const void *p, size_t n) has "
          "another signature",
          &CB);
    return;
  }
  StringRef text;
  std::string label = "sea_memdump";
  if (getConstantStringInfo(CB.getArgOperand(0), text) && !text.empty())
    label = text.str();
  else
    WARN << "sea-mlir export: sea_memdump" << where
         << ": the label is not a constant string; it prints as "
            "\"sea_memdump\"";
  if (refs.size() != 1) {
    WARN << "sea-mlir export: sea_memdump" << where << " (" << label
         << "): the shadow memory gives the call " << refs.size()
         << " memory regions, not one; it is not printed";
    return;
  }
  auto p = val(CB.getArgOperand(1), CB);
  auto n = val(CB.getArgOperand(2), CB);
  auto nTy = type(CB.getArgOperand(2)->getType(), &CB);
  if (!p || !n || !nTy)
    return;
  os << "  sea.print.mem " << quote(label) << " " << refs[0] << "[" << *p
     << "], " << *n << " : " << memTy << ", " << *nTy
     << " -> i8 {fmt = \"hexdump\"}" << l << "\n";
}

void Exporter::exportBranch(const BasicBlock &from, const BasicBlock &to,
                            const Instruction &at, std::string &text) {
  // The branch target with the values `from` passes to its phis.
  text = blockName(&to);
  SmallVector<std::string> args, types;
  for (const PHINode &phi : to.phis()) {
    const Value *in = phi.getIncomingValueForBlock(&from);
    auto v = val(in, at);
    if (!v)
      return;
    args.push_back(*v);
    if (isMem(&phi))
      types.push_back(memTy);
    else if (auto t = type(phi.getType(), &phi))
      types.push_back(*t);
  }
  if (args.empty())
    return;
  text += "(" + join(args, ", ") + " : " + join(types, ", ") + ")";
}

/// Vectors are bit-vectors: only instructions that do not depend on lanes
/// (or that SeaHorn defines on bits: insert / extractelement) are exported;
/// a lane-wise op as one wide op would be wrong (carries across lanes).
bool Exporter::vectorOk(const Instruction &I) {
  auto isVec = [](const Value *v) { return v->getType()->isVectorTy(); };
  if (!isVec(&I) && llvm::none_of(I.operands(), isVec))
    return true;
  if (isa<ExtractElementInst, InsertElementInst, PHINode>(&I))
    return true;
  if (isa<BitCastInst>(&I))
    return true; // checked by the cast export
  if (auto *sel = dyn_cast<SelectInst>(&I); sel && !isVec(sel->getCondition()))
    return true;
  // in memory, lanes of whole bytes lie at increasing addresses
  // (little-endian), as the bits of the bit-vector
  Type *t = isa<StoreInst>(&I) ? I.getOperand(0)->getType() : I.getType();
  if (isa<LoadInst, StoreInst>(&I) && t->getScalarSizeInBits() % 8 == 0)
    return true;
  error("vector operation not supported (sea vectors are bit-vectors: "
        "only insert/extractelement, bitcast, select, phi, whole-byte "
        "load/store)",
        &I);
  return false;
}

/// insert/extractelement with a constant index, on the bit-vector, as in
/// SeaHorn (BvOpSem2.cc:2079-2087, which also rejects a variable index):
/// sea.extract of the lane; insert = concat of the lanes above, the new
/// lane, and the lanes below.
void Exporter::exportVectorElement(const Instruction &I) {
  std::string l = loc(I);
  bool insert = isa<InsertElementInst>(&I);
  const Value *vec = I.getOperand(0), *idx = I.getOperand(insert ? 2 : 1);
  auto *vt = cast<FixedVectorType>(vec->getType());
  unsigned k = vt->getScalarSizeInBits(), w = k * vt->getNumElements();
  auto *ci = dyn_cast<ConstantInt>(idx);
  if (!ci) {
    error("insert/extractelement with a variable index is not supported "
          "(nor in SeaHorn)",
          &I);
    return;
  }
  if (ci->getValue().uge(vt->getNumElements())) {
    error("insert/extractelement index out of range (poison)", &I);
    return;
  }
  unsigned off = k * ci->getZExtValue();
  std::string t = "i" + std::to_string(w);
  auto v = val(vec, I);
  if (!v)
    return;
  auto extract = [&](unsigned lo, unsigned pw) {
    std::string r = fresh();
    os << "  " << r << " = sea.extract " << *v << "[" << lo << "] : " << t
       << " -> i" << pw << l << "\n";
    return r;
  };
  if (!insert) {
    names[&I] = k == w ? *v : extract(off, k);
    return;
  }
  auto x = val(I.getOperand(1), I);
  if (!x)
    return;
  SmallVector<std::pair<std::string, unsigned>> parts;
  if (off)
    parts.push_back({extract(0, off), off});
  parts.push_back({*x, k});
  if (off + k < w)
    parts.push_back({extract(off + k, w - off - k), w - off - k});
  names[&I] = concatParts(parts, l);
}

void Exporter::exportInst(const Instruction &I) {
  std::string l = loc(I);
  auto def = [&](const std::string &text) {
    std::string n = fresh();
    os << "  " << n << " = " << text << l << "\n";
    names[&I] = n;
  };
  auto bin = [&](StringRef op) {
    auto a = val(I.getOperand(0), I), b = val(I.getOperand(1), I);
    if (!a || !b)
      return;
    // nsw / nuw become sea's no-wrap promises (add, sub, mul, shl); other
    // poison-generating flags (exact, disjoint, ...) are dropped: the value
    // is the same, as in SeaHorn.
    std::string flags;
    if (auto *ob = dyn_cast<OverflowingBinaryOperator>(&I)) {
      if (ob->hasNoSignedWrap())
        flags += " nsw";
      if (ob->hasNoUnsignedWrap())
        flags += " nuw";
    }
    def(("sea." + op + " " + *a + ", " + *b + flags + " : " +
         *type(I.getType(), &I))
            .str());
  };
  if (!vectorOk(I))
    return;
  // Floating point is not modeled: an op computing on floats (arithmetic,
  // fcmp, conversions to or from floats) gives a nondet value of its
  // result type. Loads, stores, phis, selects and same-width bitcasts
  // carry the bits.
  auto isFP = [](const Value *v) { return v->getType()->isFPOrFPVectorTy(); };
  if ((isFP(&I) || llvm::any_of(I.operands(), isFP)) &&
      !isa<LoadInst, StoreInst, PHINode, SelectInst, BitCastInst, CallBase>(
          &I)) {
    warnOnce("float", "floating point is not modeled: the results of float "
                      "arithmetic, comparisons and conversions are nondet (as "
                      "in SeaHorn)");
    auto t = type(I.getType(), &I);
    if (!t)
      return;
    def("sea.nondet \"float\" [" + std::to_string(site(&I)) + "] : " + *t);
    return;
  }
  if (isa<ExtractElementInst, InsertElementInst>(&I)) {
    exportVectorElement(I);
    return;
  }
  switch (I.getOpcode()) {
  case Instruction::Add:
    return bin("add");
  case Instruction::Sub:
    return bin("sub");
  case Instruction::Mul:
    return bin("mul");
  case Instruction::UDiv:
    return bin("udiv");
  case Instruction::SDiv:
    return bin("sdiv");
  case Instruction::URem:
    return bin("urem");
  case Instruction::SRem:
    return bin("srem");
  case Instruction::And:
    return bin("and");
  case Instruction::Or:
    return bin("or");
  case Instruction::Xor:
    return bin("xor");
  case Instruction::Shl:
    return bin("shl");
  case Instruction::LShr:
    return bin("lshr");
  case Instruction::AShr:
    return bin("ashr");
  default:
    break;
  }
  if (auto *cmp = dyn_cast<ICmpInst>(&I)) {
    StringRef pred = ICmpInst::getPredicateName(cmp->getPredicate());
    auto a = val(I.getOperand(0), I), b = val(I.getOperand(1), I);
    if (!a || !b)
      return;
    Type *t = I.getOperand(0)->getType();
    if (t->isPointerTy())
      def(("sea.ptr.cmp " + pred + ", " + *a + ", " + *b + " : " + ptrTy).str());
    else if (t->isIntegerTy())
      def(("sea.icmp " + pred + ", " + *a + ", " + *b + " : " + *type(t, &I))
              .str());
    else
      error("vector icmp is not supported", &I);
    return;
  }
  if (auto *sel = dyn_cast<SelectInst>(&I)) {
    auto c = val(sel->getCondition(), I), a = val(sel->getTrueValue(), I),
         b = val(sel->getFalseValue(), I);
    auto t = type(I.getType(), &I);
    if (c && a && b && t)
      def("sea.select " + *c + ", " + *a + ", " + *b + " : " + *t);
    return;
  }
  if (auto *cast = dyn_cast<CastInst>(&I)) {
    auto a = val(I.getOperand(0), I);
    if (!a)
      return;
    Type *from = cast->getSrcTy(), *to = cast->getDestTy();
    switch (cast->getOpcode()) {
    case Instruction::ZExt:
    case Instruction::SExt:
    case Instruction::Trunc:
      def(("sea." + StringRef(cast->getOpcodeName()) + " " + *a + " : " +
           *type(from, &I) + " to " + *type(to, &I))
              .str());
      return;
    case Instruction::BitCast:
    case Instruction::AddrSpaceCast:
      if (from == to || (from->isPointerTy() && to->isPointerTy())) {
        names[&I] = *a;
        return;
      }
      // integers, integer vectors and floats of one width are the same
      // bit-vector
      if ((from->isIntOrIntVectorTy() || from->isFloatingPointTy()) &&
          (to->isIntOrIntVectorTy() || to->isFloatingPointTy()) &&
          from->getPrimitiveSizeInBits() == to->getPrimitiveSizeInBits()) {
        names[&I] = *a;
        return;
      }
      break;
    case Instruction::PtrToInt: {
      std::string i = fresh();
      os << "  " << i << " = sea.ptr.to_int " << *a << " : " << ptrTy
         << " to i" << W << l << "\n";
      unsigned w = to->getIntegerBitWidth();
      if (w == W)
        names[&I] = i;
      else
        def("sea." + std::string(w < W ? "trunc " : "zext ") + i + " : i" +
            std::to_string(W) + " to i" + std::to_string(w));
      return;
    }
    case Instruction::IntToPtr: {
      unsigned w = from->getIntegerBitWidth();
      std::string i = *a;
      if (w != W) {
        i = fresh();
        os << "  " << i << " = sea." << (w < W ? "zext " : "trunc ") << *a
           << " : i" << w << " to i" << W << l << "\n";
      }
      def("sea.ptr.from_int " + i + " : i" + std::to_string(W) + " to " +
          ptrTy);
      return;
    }
    default:
      break;
    }
    error("unsupported cast", &I);
    return;
  }
  if (auto *ev = dyn_cast<ExtractValueInst>(&I)) {
    auto it = overflowParts.find(ev->getAggregateOperand());
    if (it != overflowParts.end()) {
      names[&I] = ev->getIndices()[0] == 0 ? it->second.first
                                           : it->second.second;
      return;
    }
    // a chain of sea.struct.extract along the index path
    auto cur = val(ev->getAggregateOperand(), I);
    Type *t = ev->getAggregateOperand()->getType();
    for (unsigned idx : ev->getIndices()) {
      if (!cur)
        return;
      auto from = type(t, &I);
      t = GetElementPtrInst::getTypeAtIndex(t, idx);
      auto to = type(t, &I);
      if (!from || !to)
        return;
      std::string n = fresh();
      os << "  " << n << " = sea.struct.extract " << *cur << "[" << idx
         << "] : " << *from << " -> " << *to << l << "\n";
      cur = n;
    }
    if (cur)
      names[&I] = *cur;
    return;
  }
  if (auto *iv = dyn_cast<InsertValueInst>(&I)) {
    // extract the structs along the path, insert bottom-up
    auto agg = val(iv->getAggregateOperand(), I),
         v = val(iv->getInsertedValueOperand(), I);
    if (!agg || !v)
      return;
    ArrayRef<unsigned> path = iv->getIndices();
    std::vector<std::string> outer{*agg};
    std::vector<Type *> types{iv->getType()};
    for (unsigned d = 0; d + 1 < path.size(); ++d) {
      Type *inner = GetElementPtrInst::getTypeAtIndex(types.back(), path[d]);
      auto from = type(types.back(), &I), to = type(inner, &I);
      if (!from || !to)
        return;
      std::string n = fresh();
      os << "  " << n << " = sea.struct.extract " << outer.back() << "["
         << path[d] << "] : " << *from << " -> " << *to << l << "\n";
      outer.push_back(n);
      types.push_back(inner);
    }
    std::string cur = *v;
    for (unsigned d = path.size(); d-- > 0;) {
      Type *field = GetElementPtrInst::getTypeAtIndex(types[d], path[d]);
      auto ft = type(field, &I), st = type(types[d], &I);
      if (!ft || !st)
        return;
      std::string n = fresh();
      os << "  " << n << " = sea.struct.insert " << cur << ", " << outer[d]
         << "[" << path[d] << "] : " << *ft << " into " << *st << l << "\n";
      cur = n;
    }
    names[&I] = cur;
    return;
  }
  if (isa<FreezeInst>(&I)) {
    if (auto a = val(I.getOperand(0), I))
      names[&I] = *a;
    return;
  }
  if (auto *gep = dyn_cast<GetElementPtrInst>(&I)) {
    if (auto n = exportGep(cast<GEPOperator>(*gep), I))
      names[&I] = *n;
    return;
  }
  if (auto *al = dyn_cast<AllocaInst>(&I)) {
    uint64_t elt = DL.getTypeAllocSize(al->getAllocatedType());
    std::optional<std::string> size;
    if (auto *c = dyn_cast<ConstantInt>(al->getArraySize()))
      size = emitConst(APInt(W, elt * c->getZExtValue()), l);
    else if (auto n = sizeVal(al->getArraySize(), I)) {
      std::string e = emitConst(APInt(W, elt), l);
      size = fresh();
      os << "  " << *size << " = sea.mul " << *n << ", " << e << " : i" << W
         << l << "\n";
    }
    if (!size)
      return;
    def("sea.alloca " + *size + " align " +
        std::to_string(objectAlign(al->getAlign(), W / 8)) + " [" +
        std::to_string(site(&I)) + "] : i" + std::to_string(W) + " -> " +
        ptrTy);
    // Allocation is a definition (--horn-shadow-mem-alloc-is-def): the
    // contents do not change.
    if (pendingDef) {
      auto d = *takeDef(I);
      names[d.second] = d.first;
    }
    return;
  }
  if (isa<LoadInst, StoreInst>(&I) &&
      isa<StructType, ArrayType>(getLoadStoreType(const_cast<Instruction *>(&I)))) {
    error("loads and stores of aggregates are not supported yet", &I);
    return;
  }
  // LLVM's alignment promise, in bytes (sea `align`; 1 says nothing).
  auto align = [](Align a) -> std::string {
    return a.value() == 1 ? "" : " align " + std::to_string(a.value());
  };
  if (auto *ld = dyn_cast<LoadInst>(&I)) {
    auto m = takeUse(I);
    auto p = val(ld->getPointerOperand(), I);
    if (!m || !p)
      return;
    Type *t = ld->getType();
    if (t->isIntegerTy() && t->getIntegerBitWidth() % 8 != 0) {
      // i1 and friends occupy whole bytes in memory
      unsigned w = t->getIntegerBitWidth(), bw = (w + 7) / 8 * 8;
      std::string b = fresh();
      os << "  " << b << " = sea.load " << *m << "[" << *p << "]"
         << align(ld->getAlign()) << " : " << memTy
         << " -> i" << bw << l << "\n";
      def("sea.trunc " + b + " : i" + std::to_string(bw) + " to i" +
          std::to_string(w));
      return;
    }
    if (auto ty = type(t, &I))
      def("sea.load " + *m + "[" + *p + "]" + align(ld->getAlign()) + " : " +
          memTy + " -> " + *ty);
    return;
  }
  if (auto *st = dyn_cast<StoreInst>(&I)) {
    auto d = takeDef(I);
    auto p = val(st->getPointerOperand(), I), v = val(st->getValueOperand(), I);
    if (!d || !p || !v)
      return;
    Type *t = st->getValueOperand()->getType();
    std::string value = *v, vty;
    if (t->isIntegerTy() && t->getIntegerBitWidth() % 8 != 0) {
      unsigned w = t->getIntegerBitWidth(), bw = (w + 7) / 8 * 8;
      value = fresh();
      os << "  " << value << " = sea.zext " << *v << " : i" << w << " to i"
         << bw << l << "\n";
      vty = "i" + std::to_string(bw);
    } else if (auto ty = type(t, &I)) {
      vty = *ty;
    } else {
      return;
    }
    std::string r = fresh();
    os << "  " << r << " = sea.store " << d->first << "[" << *p << "], "
       << value << " inplace" << align(st->getAlign()) << " : " << memTy
       << ", " << vty << l << "\n";
    names[d->second] = r;
    return;
  }
  if (auto *cb = dyn_cast<CallBase>(&I))
    return exportCall(*cb);
  error(Twine("unsupported instruction ") + I.getOpcodeName(), &I);
}

void Exporter::exportBlock(const BasicBlock &BB) {
  // block header: phis become block arguments
  SmallVector<std::string> args;
  for (const PHINode &phi : BB.phis()) {
    std::string n = fresh();
    names[&phi] = n;
    if (isMem(&phi))
      args.push_back(n + " : " + memTy);
    else if (auto t = type(phi.getType(), &phi))
      args.push_back(n + " : " + *t);
  }
  os << blockName(&BB);
  if (!args.empty())
    os << "(" << join(args, ", ") << ")";
  os << ":\n";

  for (const Instruction &I : BB) {
    if (isa<PHINode>(I))
      continue;
    if (I.isTerminator())
      break;
    exportInst(I);
  }
  if (pendingDef || pendingUse || pendingTrsfr)
    error("shadow memory call without the memory instruction it belongs to "
          "in block " +
          BB.getName());
  pendingDef.reset();
  pendingUse.reset();
  pendingTrsfr.reset();

  const Instruction *term = BB.getTerminator();
  std::string l = loc(*term);
  if (isa<ReturnInst>(term)) {
    // BMC checks reachability of the return block.
    std::string f = fresh();
    os << "  " << f << " = sea.const 0 : i1" << l << "\n";
    os << "  sea.assert " << f << l << "\n  sea.halt" << l << "\n";
    return;
  }
  if (isa<UnreachableInst>(term)) {
    os << "  sea.unreachable" << l << "\n";
    return;
  }
  if (auto *br = dyn_cast<BranchInst>(term)) {
    if (br->isUnconditional()) {
      std::string t;
      exportBranch(BB, *br->getSuccessor(0), *term, t);
      os << "  sea.br " << t << l << "\n";
      return;
    }
    auto c = val(br->getCondition(), *term);
    std::string t, e;
    exportBranch(BB, *br->getSuccessor(0), *term, t);
    exportBranch(BB, *br->getSuccessor(1), *term, e);
    if (c)
      os << "  sea.cond_br " << *c << ", " << t << ", " << e << l << "\n";
    return;
  }
  if (auto *sw = dyn_cast<SwitchInst>(term)) {
    // A chain of tests, one block per case.
    auto c = val(sw->getCondition(), *term);
    if (!c)
      return;
    std::string ty = *type(sw->getCondition()->getType(), term);
    unsigned k = 0;
    for (auto cs : sw->cases()) {
      std::string v = emitConst(cs.getCaseValue()->getValue(), l);
      std::string eq = fresh();
      os << "  " << eq << " = sea.icmp eq, " << *c << ", " << v << " : " << ty
         << l << "\n";
      std::string t, next = blockName(&BB) + "_sw" + std::to_string(k++);
      exportBranch(BB, *cs.getCaseSuccessor(), *term, t);
      os << "  sea.cond_br " << eq << ", " << t << ", " << next << l << "\n";
      os << next << ":\n";
    }
    std::string d;
    exportBranch(BB, *sw->getDefaultDest(), *term, d);
    os << "  sea.br " << d << l << "\n";
    return;
  }
  error(Twine("unsupported terminator ") + term->getOpcodeName(), term);
}

bool Exporter::run() {
  findMemValues();
  unsigned rets = 0;
  for (const BasicBlock &BB : F)
    rets += isa<ReturnInst>(BB.getTerminator());
  if (rets != 1) {
    error("expected one return block, found " + Twine(rets));
    return false;
  }
  // Reverse post-order: in loop-free code every value is defined before it is
  // used, including the values branches pass to phis.
  ReversePostOrderTraversal<const Function *> rpo(&F);
  for (const BasicBlock *BB : rpo)
    blockName(BB);
  for (const BasicBlock *BB : rpo)
    exportBlock(*BB);
  if (!ok)
    return false;
  out << "// Exported from SeaHorn (" << F.getParent()->getModuleIdentifier()
      << ", function " << F.getName() << ").\n";
  out << "sea.program @" << quote(F.getName()) << " {\n";
  if (llvmLinks)
    placePositions(body);
  out << os.str();
  out << "}\n";
  return true;
}

} // namespace

bool exportSeaMlir(const Function &F, raw_ostream &out, SeaMlirSites &sites,
                   bool llvmLinks, StringRef mlirPath) {
  return Exporter(F, out, sites, llvmLinks, mlirPath).run();
}

/// --horn-sea-mlir-export-only: ends the process after the export, with
/// status 0 if it succeeded and 1 otherwise (a harness can test the status;
/// without the option a failed export only prints errors).
static void exportOnlyExit(bool ok, StringRef path) {
  if (ok)
    outs() << "sea-mlir-export: wrote " << path << "\n";
  else
    errs() << "sea-mlir-export: export failed (see the errors above)\n";
  outs().flush();
  errs().flush();
  std::exit(ok ? 0 : 1);
}

PreservedAnalyses SeaMlirPrepPass::run(Module &M, ModuleAnalysisManager &) {
  Function *f = M.getFunction("sea_memdump");
  if (!f || !f->isDeclaration() || f->arg_size() != 3 ||
      !f->getArg(1)->getType()->isPointerTy())
    return PreservedAnalyses::all();
  // the body reads *p: the shadow memory gives each call a use of p's
  // region (no new version); the exporter prints the call, never the body
  LLVMContext &ctx = M.getContext();
  BasicBlock *bb = BasicBlock::Create(ctx, "entry", f);
  IRBuilder<> b(bb);
  b.CreateLoad(Type::getInt8Ty(ctx), f->getArg(1), "byte");
  if (f->getReturnType()->isVoidTy())
    b.CreateRetVoid();
  else
    b.CreateRet(UndefValue::get(f->getReturnType()));
  f->addFnAttr(Attribute::NoInline);
  f->setLinkage(GlobalValue::InternalLinkage);
  return PreservedAnalyses::none();
}

PreservedAnalyses SeaMlirEnginePass::run(Module &M, ModuleAnalysisManager &) {
  auto fail = [](const Twine &msg) {
    ERR << "sea-mlir engine: " << msg;
    if (SeaMlirExportOnly)
      exportOnlyExit(false, "");
    return PreservedAnalyses::all();
  };
  // The front end may decide every assertion before the export: it removes
  // main, or leaves a main that cannot reach seahorn.fail (no call to it,
  // and no call to a defined function that could). BMC's query (reach the
  // return block, which the pipeline makes reachable only through
  // seahorn.fail) does not hold for such a main: exporting it as is would
  // assert false on every path (a false sat). Then the export writes a
  // trivial program, `sea.assert true` before the halt (sea-vc: unsat).
  std::string decided;
  Function *main = M.getFunction("main");
  if (!main || main->isDeclaration()) {
    decided = "no main after the pipeline (the front end removed it: every "
              "assertion was decided before export)";
  } else {
    bool canFail = false;
    for (const Instruction &I : instructions(*main))
      if (auto *cb = dyn_cast<CallBase>(&I)) {
        if (const Function *f = calledFunction(*cb))
          canFail |= f->getName() == "seahorn.fail" ||
                     (!f->isDeclaration() && f->getName() != "sea_memdump");
        else
          // an indirect call may reach seahorn.fail: not decided
          canFail |= !cb->isInlineAsm();
      }
    if (!canFail)
      decided = "main cannot reach seahorn.fail after the pipeline (the "
                "front end decided every assertion before export)";
  }
  if (!decided.empty())
    outs() << "sea-mlir-export: " << decided << "\n";

  // Export.
  SmallString<128> path(SeaMlirOut);
  if (path.empty()) {
    int fd;
    if (sys::fs::createTemporaryFile("sea", "mlir", fd, path))
      return fail("cannot create a temporary file");
    sys::Process::SafelyCloseFileDescriptor(fd);
  }
  SeaMlirSites sites;
  {
    std::error_code ec;
    raw_fd_ostream file(path, ec);
    if (ec)
      return fail(Twine("cannot write ") + path + ": " + ec.message());
    if (!decided.empty())
      file << "// sea-mlir-export: " << decided << "\n"
           << "sea.program @\"main\" {\n"
           << "  %v0 = sea.const 1 : i1\n"
           << "  sea.assert %v0\n"
           << "  sea.halt\n"
           << "}\n";
    else if (!exportSeaMlir(*main, file, sites, !SeaMlirLlOut.empty(), path))
      return fail("export failed");
  }
  // --horn-sea-mlir-ll-out: the module the links refer to, as exported
  if (!SeaMlirLlOut.empty()) {
    std::error_code ec;
    raw_fd_ostream ll(SeaMlirLlOut, ec);
    if (ec)
      return fail(Twine("cannot write ") + SeaMlirLlOut + ": " + ec.message());
    M.print(ll, nullptr);
  }
  if (SeaMlirExportOnly)
    exportOnlyExit(true, path);
  if (!m_solve)
    return PreservedAnalyses::all();

  // Run sea-vc and read its verdict.
  auto vc = sys::findProgramByName(SeaVcPath);
  if (!vc) {
    ERR << "sea-mlir engine: cannot find " << SeaVcPath
        << " (set --horn-sea-vc)";
    return PreservedAnalyses::all();
  }
  SmallString<128> outPath;
  int fd;
  if (sys::fs::createTemporaryFile("sea-vc", "out", fd, outPath)) {
    ERR << "sea-mlir engine: cannot create a temporary file";
    return PreservedAnalyses::all();
  }
  sys::Process::SafelyCloseFileDescriptor(fd);
  // SeaHorn's word size (--horn-bv2-word-size, by default the pointer
  // size): sea-mlir widens, per memory, the byte memories whose accesses are
  // all aligned whole words; the others stay bytes (sea-widen-memory).
  unsigned word = 0;
  {
    auto &opts = cl::getRegisteredOptions();
    if (auto it = opts.find("horn-bv2-word-size"); it != opts.end())
      word = static_cast<cl::opt<unsigned> *>(it->second)->getValue();
    if (word == 0)
      word = M.getDataLayout().getPointerSize(0);
  }
  std::string widen = "--widen-memory=" + std::to_string(word);
  SmallVector<StringRef> args = {*vc, path, "--lower"};
  if (word > 1)
    args.push_back(widen);
  for (const std::string &a : SeaVcArgs)
    args.push_back(a);
  std::optional<StringRef> redirects[] = {std::nullopt, StringRef(outPath),
                                          std::nullopt};
  std::string err;
  int rc = sys::ExecuteAndWait(*vc, args, std::nullopt, redirects, 0, 0, &err);
  auto buf = MemoryBuffer::getFile(outPath);
  sys::fs::remove(outPath);
  std::string result = "unknown";
  if (buf)
    for (StringRef line = (*buf)->getBuffer(); !line.empty();) {
      auto [first, rest] = line.split('\n');
      if (first.consume_front("result: "))
        result = first.str();
      // sea-vc --brunch-stats (in --horn-sea-vc-arg): the statistics survive
      // the engine
      if (first.starts_with("BRUNCH_STAT "))
        outs() << first << "\n";
      line = rest;
    }
  // Only these statuses carry a verdict (sea-vc --agent, STATUS CODES):
  // 0 = unsat, or sat confirmed by replay; 3 = unknown. Anything else is no
  // verdict, whatever `result:` says: 2 = the replay disagrees with the model
  // (a bug in sea-mlir's VC or interpreter), 4 = --seam sat on an execution
  // that leaves an object (A-INB, assumed, does not hold: inconclusive, the
  // program has a memory-safety error), 1 = error.
  bool verdict = rc == 0 || (rc == 3 && result == "unknown");
  if (!verdict) {
    ERR << "sea-mlir engine: sea-vc exited with " << rc << " " << err;
    if (rc == 2)
      ERR << "sea-mlir engine: sea-vc's replay disagrees with its model; "
             "no verdict";
    else if (rc == 4)
      ERR << "sea-mlir engine: sea-vc's sat needs an out-of-bounds access "
             "(A-INB does not hold); inconclusive";
    result = "unknown";
  }
  outs() << result << "\n";
  return PreservedAnalyses::all();
}

} // namespace seahorn
