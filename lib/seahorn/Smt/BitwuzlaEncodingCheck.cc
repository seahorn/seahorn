#ifdef WITH_BITWUZLA

#include "seahorn/Expr/Smt/BitwuzlaEncodingCheck.hh"
#include "seahorn/Expr/ExprLlvm.hh"

#include <unordered_set>
#include <vector>

using namespace expr;

namespace seahorn {
namespace solver {

/// Bool is width 0. Sets \p ok to false for any other sort.
static unsigned widthOf(const bitwuzla::Sort &s, bool &ok) {
  ok = true;
  if (s.is_bool())
    return 0;
  if (s.is_bv())
    return s.bv_size();
  ok = false;
  return 0;
}

/// Why Z3 might read \p name, as Bitwuzla prints it, as another name; or
/// nullptr. SMT-LIB cannot quote '|' or '\\', Bitwuzla prints a name that
/// looks quoted (|x|) as it is, and its let-bound names are _let0, _let1, ...
static const char *unsafeName(const std::string &name) {
  if (name.find('|') != std::string::npos ||
      name.find('\\') != std::string::npos)
    return "contains | or \\";
  if (name.compare(0, 4, "_let") == 0)
    return "may be taken for one of Bitwuzla's let names";
  return nullptr;
}

EncodingCheck checkBitwuzlaEncoding(Expr e, const bitwuzla::Term &t,
                                    unsigned timeout_ms) {
  using V = EncodingVerdict;
  try {
    // -- the free constants of t, with their names and sorts
    std::vector<SmtLibConst> consts;
    std::unordered_set<bitwuzla::Term> seen;
    std::vector<bitwuzla::Term> todo{t};
    while (!todo.empty()) {
      bitwuzla::Term u = todo.back();
      todo.pop_back();
      if (!seen.insert(u).second)
        continue;
      if (u.is_variable())
        return {V::UNCHECKED, "the term has a bound variable"};
      if (u.is_const()) {
        auto name = u.symbol();
        if (!name)
          return {V::UNCHECKED, "a constant has no name: " + u.str()};
        if (const char *why = unsafeName(name->get()))
          return {V::UNCHECKED,
                  "the name of constant " + name->get() + " " + why};
        bool ok;
        unsigned w = widthOf(u.sort(), ok);
        if (!ok)
          return {V::UNCHECKED, "a constant of sort " + u.sort().str() +
                                    " is not supported by the check"};
        consts.push_back({name->get(), w});
      }
      for (const bitwuzla::Term &ch : u.children())
        todo.push_back(ch);
    }

    bool ok;
    unsigned w = widthOf(t.sort(), ok);
    if (!ok)
      return {V::UNCHECKED, "a term of sort " + t.sort().str() +
                                " is not supported by the check"};
    // -- printed by Bitwuzla, in SMT-LIB with let for shared subterms
    return checkSmtLibTermWithZ3(e, t.str(), consts, w, timeout_ms);
  } catch (std::exception &ex) {
    return {V::UNCHECKED, std::string("Bitwuzla failed: ") + ex.what()};
  }
}

} // namespace solver
} // namespace seahorn

#endif
