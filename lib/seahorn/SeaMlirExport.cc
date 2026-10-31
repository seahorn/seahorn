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
/// - global initializers are ignored (globals start uninitialized), with a
///   warning per global;
/// - calls to external functions without a shadow-memory definition are
///   no-ops returning a nondet value (as BvOpSem2), with a warning per
///   callee.
/// Anything else is an error.

#include "seahorn/SeaMlirExport.hh"

#include "seahorn/Support/SeaDebug.h"
#include "seahorn/Support/SeaLog.hh"

#include "llvm/ADT/DenseMap.h"
#include "llvm/ADT/PostOrderIterator.h"
#include "llvm/ADT/StringExtras.h"
#include "llvm/ADT/DenseSet.h"
#include "llvm/ADT/StringSet.h"
#include "llvm/IR/Constants.h"
#include "llvm/IR/DataLayout.h"
#include "llvm/IR/DebugInfoMetadata.h"
#include "llvm/IR/Function.h"
#include "llvm/IR/CFG.h"
#include "llvm/IR/GetElementPtrTypeIterator.h"
#include "llvm/IR/InlineAsm.h"
#include "llvm/IR/InstIterator.h"
#include "llvm/IR/Instructions.h"
#include "llvm/IR/IntrinsicInst.h"
#include "llvm/IR/Module.h"
#include "llvm/Support/CommandLine.h"
#include "llvm/Support/FileSystem.h"
#include "llvm/Support/MemoryBuffer.h"
#include "llvm/Support/Process.h"
#include "llvm/Support/Program.h"
#include "llvm/Support/raw_ostream.h"

#include <optional>

using namespace llvm;

static cl::opt<std::string> SeaMlirOut(
    "horn-sea-mlir-out",
    cl::desc("sea-mlir engine: write the exported program to this file "
             "(default: a temporary file)"),
    cl::init(""));

static cl::opt<std::string>
    SeaVcPath("horn-sea-vc", cl::desc("sea-mlir engine: the sea-vc tool"),
              cl::init("sea-vc"));

static cl::list<std::string>
    SeaVcArgs("horn-sea-vc-arg",
              cl::desc("sea-mlir engine: an extra argument for sea-vc"));

namespace seahorn {
namespace {

/// Escapes a string for an MLIR string literal.
std::string quote(StringRef s) {
  std::string r = "\"";
  for (char c : s) {
    if (c == '"' || c == '\\')
      r += '\\';
    r += c;
  }
  return r + "\"";
}

class Exporter {
public:
  Exporter(const Function &F, raw_ostream &out, SeaMlirSites &sites)
      : F(F), DL(F.getParent()->getDataLayout()), out(out), sites(sites),
        os(body) {
    W = DL.getPointerSizeInBits();
    ptrTy = "!sea.ptr<" + std::to_string(W) + ">";
    memTy = "!sea.mem<" + ptrTy + ", i8>";
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

  // -- names and types
  std::string fresh() { return "%v" + std::to_string(next++); }
  std::optional<std::string> type(Type *t, const Value *at);
  std::string loc(const Instruction &I);
  std::string blockName(const BasicBlock *BB) {
    auto it = blocks.find(BB);
    if (it == blocks.end())
      it = blocks.try_emplace(BB, "^bb" + std::to_string(blocks.size())).first;
    return it->second;
  }

  // -- operands: emits code for constants and returns the operand's name
  std::optional<std::string> val(const Value *v, const Instruction &at);
  std::optional<std::string> constant(const Constant *c, const Instruction &at);
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
  void exportInst(const Instruction &I);
  void exportCall(const CallBase &CB);
  void exportShadow(const CallBase &CB, StringRef name);
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
  // shadow memory: pending definition and uses for the next memory op
  std::optional<std::pair<std::string, const Value *>> pendingDef;
  std::optional<std::string> pendingUse;
  std::optional<std::string> pendingTrsfr;
};

std::optional<std::string> Exporter::type(Type *t, const Value *at) {
  if (auto *it = dyn_cast<IntegerType>(t))
    return "i" + std::to_string(it->getBitWidth());
  if (t->isPointerTy())
    return ptrTy;
  std::string s;
  raw_string_ostream ts(s);
  ts << *t;
  error("unsupported type " + s, at);
  return std::nullopt;
}

std::string Exporter::loc(const Instruction &I) {
  std::string child;
  if (const DebugLoc &dl = I.getDebugLoc()) {
    if (auto *scope = dyn_cast<DIScope>(dl.getScope()))
      child = quote(scope->getFilename()) + ":" + std::to_string(dl.getLine()) +
              ":" + std::to_string(dl.getCol());
  }
  if (I.hasName()) {
    std::string n = quote(I.getName());
    return " loc(" + (child.empty() ? n : n + "(" + child + ")") + ")";
  }
  if (!child.empty())
    return " loc(" + child + ")";
  return "";
}

void Exporter::findMemValues() {
  for (const Instruction &I : instructions(F))
    if (auto *cb = dyn_cast<CallBase>(&I))
      if (const Function *f = cb->getCalledFunction())
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
  std::string l = loc(at);
  if (auto *ci = dyn_cast<ConstantInt>(c))
    return emitConst(ci->getValue(), l);
  if (isa<ConstantPointerNull>(c)) {
    std::string n = fresh();
    os << "  " << n << " = sea.ptr.null : " << ptrTy << l << "\n";
    return n;
  }
  if (auto *gv = dyn_cast<GlobalVariable>(c)) {
    if (gv->hasInitializer())
      warnOnce("init:" + gv->getName(),
               "the initializer of global " + gv->getName() +
                   " is ignored: globals start uninitialized");
    std::string n = fresh();
    uint64_t size = DL.getTypeAllocSize(gv->getValueType());
    os << "  " << n << " = sea.global @" << quote(gv->getName()) << " size "
       << size << " align " << gv->getPointerAlignment(DL).value() << " : "
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
  if (isa<UndefValue>(c)) {
    error("undef/poison operands are not supported", &at);
    return std::nullopt;
  }
  error("unsupported constant", c);
  return std::nullopt;
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
  std::string l = loc(at);
  auto base = val(gep.getPointerOperand(), at);
  if (!base)
    return std::nullopt;
  std::string cur = *base;
  APInt constOff(W, 0);
  auto addOffset = [&](const std::string &off) {
    std::string n = fresh();
    os << "  " << n << " = sea.ptr.add " << cur << ", " << off << " : "
       << ptrTy << ", i" << W << l << "\n";
    cur = n;
  };
  for (gep_type_iterator gti = gep_type_begin(gep), e = gep_type_end(gep);
       gti != e; ++gti) {
    const Value *idx = gti.getOperand();
    if (StructType *st = gti.getStructTypeOrNull()) {
      unsigned field = cast<ConstantInt>(idx)->getZExtValue();
      constOff += DL.getStructLayout(st)->getElementOffset(field);
      continue;
    }
    uint64_t size = gti.getSequentialElementStride(DL).getFixedValue();
    if (auto *ci = dyn_cast<ConstantInt>(idx)) {
      constOff += APInt(W, size) * ci->getValue().sextOrTrunc(W);
      continue;
    }
    if (!idx->getType()->isIntegerTy()) {
      error("vector GEP indices are not supported", &at);
      return std::nullopt;
    }
    auto i = val(idx, at);
    if (!i)
      return std::nullopt;
    unsigned iw = idx->getType()->getIntegerBitWidth();
    std::string iW = *i;
    if (iw != W) {
      iW = fresh();
      os << "  " << iW << " = sea." << (iw < W ? "sext " : "trunc ") << *i
         << " : i" << iw << " to i" << W << l << "\n";
    }
    std::string off = iW;
    if (size != 1) {
      std::string s = emitConst(APInt(W, size), l);
      off = fresh();
      os << "  " << off << " = sea.mul " << iW << ", " << s << " : i" << W << l
         << "\n";
    }
    addOffset(off);
  }
  if (!constOff.isZero())
    addOffset(emitConst(constOff, l));
  return cur;
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
    // Globals start uninitialized: the version passes through.
    auto in = val(CB.getArgOperand(1), CB);
    if (in)
      names[&CB] = *in;
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
    if (v)
      pendingUse = *v;
    return;
  }
  if (name == "shadow.mem.trsfr.load") {
    auto v = val(CB.getArgOperand(1), CB);
    if (v)
      pendingTrsfr = *v;
    return;
  }
  error("unsupported shadow memory function " + name, &CB);
}

void Exporter::exportCall(const CallBase &CB) {
  const Function *f = CB.getCalledFunction();
  if (!f) {
    if (auto *ia = dyn_cast<InlineAsm>(CB.getCalledOperand()))
      error("inline assembly is not supported: \"" + ia->getAsmString() +
                "\"",
            &CB);
    else
      error("indirect calls are not supported", &CB);
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
  if (f->isDeclaration() && CB.arg_empty() && !CB.getType()->isVoidTy() &&
      (name.starts_with("nd") || name.starts_with("nondet") ||
       name.starts_with("verifier.nondet") ||
       name.starts_with("__VERIFIER_nondet"))) {
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
  if (auto *ms = dyn_cast<MemSetInst>(&CB)) {
    auto d = takeDef(CB);
    auto p = val(ms->getDest(), CB), v = val(ms->getValue(), CB),
         n = sizeVal(ms->getLength(), CB);
    if (!d || !p || !v || !n)
      return;
    std::string r = fresh();
    os << "  " << r << " = sea.memset " << d->first << "[" << *p << "], " << *v
       << ", " << *n << " inplace : " << memTy << l << "\n";
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
       << src << "[" << *sp << "], " << *n << " inplace : " << memTy << l
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
  if (!CB.getType()->isIntegerTy()) {
    error("external call returning a non-integer is not supported", &CB);
    return;
  }
  std::string n = fresh();
  os << "  " << n << " = sea.nondet " << quote(name) << " [" << site(&CB)
     << "] : " << *type(CB.getType(), &CB) << l << "\n";
  names[&CB] = n;
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

void Exporter::exportInst(const Instruction &I) {
  std::string l = loc(I);
  auto def = [&](const std::string &text) {
    std::string n = fresh();
    os << "  " << n << " = " << text << l << "\n";
    names[&I] = n;
  };
  auto bin = [&](StringRef op) {
    auto a = val(I.getOperand(0), I), b = val(I.getOperand(1), I);
    if (a && b)
      def(("sea." + op + " " + *a + ", " + *b + " : " + *type(I.getType(), &I))
              .str());
  };
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
        std::to_string(al->getAlign().value()) + " [" +
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
      os << "  " << b << " = sea.load " << *m << "[" << *p << "] : " << memTy
         << " -> i" << bw << l << "\n";
      def("sea.trunc " + b + " : i" + std::to_string(bw) + " to i" +
          std::to_string(w));
      return;
    }
    if (auto ty = type(t, &I))
      def("sea.load " + *m + "[" + *p + "] : " + memTy + " -> " + *ty);
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
       << value << " inplace : " << memTy << ", " << vty << l << "\n";
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
  out << os.str();
  out << "}\n";
  return true;
}

} // namespace

bool exportSeaMlir(const Function &F, raw_ostream &out, SeaMlirSites &sites) {
  return Exporter(F, out, sites).run();
}

PreservedAnalyses SeaMlirEnginePass::run(Module &M, ModuleAnalysisManager &) {
  Function *main = M.getFunction("main");
  if (!main || main->isDeclaration()) {
    ERR << "sea-mlir engine: no main function";
    return PreservedAnalyses::all();
  }

  // Export.
  SmallString<128> path(SeaMlirOut);
  if (path.empty()) {
    int fd;
    if (sys::fs::createTemporaryFile("sea", "mlir", fd, path)) {
      ERR << "sea-mlir engine: cannot create a temporary file";
      return PreservedAnalyses::all();
    }
    sys::Process::SafelyCloseFileDescriptor(fd);
  }
  SeaMlirSites sites;
  {
    std::error_code ec;
    raw_fd_ostream file(path, ec);
    if (ec) {
      ERR << "sea-mlir engine: cannot write " << path << ": " << ec.message();
      return PreservedAnalyses::all();
    }
    if (!exportSeaMlir(*main, file, sites)) {
      ERR << "sea-mlir engine: export failed";
      return PreservedAnalyses::all();
    }
  }
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
  SmallVector<StringRef> args = {*vc, path, "--lower"};
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
      line = rest;
    }
  if (rc != 0 && !(rc == 3 && result == "unknown")) {
    ERR << "sea-mlir engine: sea-vc exited with " << rc << " " << err;
    if (rc == 2)
      ERR << "sea-mlir engine: sea-vc's replay disagrees with its model";
  }
  outs() << result << "\n";
  return PreservedAnalyses::all();
}

} // namespace seahorn
