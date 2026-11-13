#ifdef WITH_BITWUZLA

#include "seahorn/Expr/Smt/BitwuzlaEncodingCheck.hh"
#include "seahorn/Expr/ExprLlvm.hh"

#include <algorithm>
#include <sstream>
#include <unordered_map>
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
  if (name.compare(0, 4, "_bwc") == 0)
    return "may be taken for one of the check's definitions";
  return nullptr;
}

static bool isBinder(const bitwuzla::Term &u) {
  return u.kind() == bitwuzla::Kind::LAMBDA ||
         u.kind() == bitwuzla::Kind::FORALL ||
         u.kind() == bitwuzla::Kind::EXISTS;
}

/// Prints \p t, a term with binders, as SMT-LIB that does not depend on
/// Bitwuzla's let printing. Each closed subterm that is not a leaf gets a
/// let of its own, at the top, children first, with a name used nowhere
/// else; its definition is printed by Bitwuzla without lets, with its closed
/// subterms replaced by their names. (Not define-fun: Z3 5.1.0 has given
/// wrong answers on lambdas defined that way.)
static std::string printWithLets(const bitwuzla::Term &t,
                                 bitwuzla::TermManager &tm) {
  using bitwuzla::Term;
  // -- the free variables of every subterm, children first
  std::unordered_map<Term, std::vector<Term>> fv;
  std::vector<Term> order;
  {
    std::vector<std::pair<Term, bool>> todo{{t, false}};
    while (!todo.empty()) {
      auto [u, done] = todo.back();
      todo.pop_back();
      if (fv.count(u))
        continue;
      if (!done) {
        todo.push_back({u, true});
        for (const Term &c : u.children())
          if (!fv.count(c))
            todo.push_back({c, false});
        continue;
      }
      std::vector<Term> vs;
      if (u.is_variable())
        vs.push_back(u);
      size_t n = u.num_children(), bound = isBinder(u) ? n - 1 : 0;
      for (size_t i = 0; i < n; ++i)
        for (const Term &v : fv.at(u[i]))
          if (std::find(vs.begin(), vs.end(), v) == vs.end())
            vs.push_back(v);
      for (size_t i = 0; i < bound; ++i)
        vs.erase(std::remove(vs.begin(), vs.end(), u[i]), vs.end());
      fv[u] = vs;
      order.push_back(u);
    }
  }
  auto leaf = [](const Term &u) { return u.num_children() == 0; };
  auto closed = [&](const Term &u) { return fv.at(u).empty(); };

  // -- (forall xs (= (a xs) (b xs))) with closed a and b, as the encoder
  // -- states an equality with a function, is a = b (extensionality). Z3
  // -- decides that for arrays and lambdas, but not always the quantifier.
  // -- Sets a and b, the function or array on each side.
  auto pointwise = [&](const Term &u, Term &a, Term &b) {
    if (u.kind() != bitwuzla::Kind::FORALL)
      return false;
    size_t n = u.num_children();
    const Term body = u[n - 1];
    if (body.kind() != bitwuzla::Kind::EQUAL)
      return false;
    Term sides[2];
    for (int k = 0; k < 2; ++k) {
      const Term side = body[k];
      if (side.kind() == bitwuzla::Kind::APPLY && side.num_children() == n) {
        for (size_t i = 1; i < n; ++i)
          if (side[i] != u[i - 1])
            return false;
      } else if (side.kind() == bitwuzla::Kind::ARRAY_SELECT && n == 2) {
        if (side[1] != u[0])
          return false;
      } else {
        return false;
      }
      if (!closed(side[0]))
        return false;
      sides[k] = side[0];
    }
    a = sides[0];
    b = sides[1];
    return true;
  };

  std::unordered_map<Term, Term> name;
  unsigned count = 0;
  std::string lets, closing;
  for (const Term &u : order) {
    if (leaf(u) || !closed(u))
      continue;
    // -- the closed subterms right below u (for a binder, the maximal
    // -- closed subterms of its body) are replaced by their names
    std::unordered_map<Term, Term> subst;
    std::vector<Term> todo;
    for (size_t i = isBinder(u) ? u.num_children() - 1 : 0;
         i < u.num_children(); ++i)
      todo.push_back(u[i]);
    std::unordered_set<Term> seen;
    while (!todo.empty()) {
      Term c = todo.back();
      todo.pop_back();
      if (!seen.insert(c).second || leaf(c))
        continue;
      if (closed(c)) {
        subst.emplace(c, name.at(c));
        continue;
      }
      for (const Term &g : c.children())
        todo.push_back(g);
    }
    std::string kname = "_bwc" + std::to_string(++count);
    std::ostringstream os;
    Term a, b;
    if (pointwise(u, a, b)) {
      auto text = [&](const Term &x) {
        return leaf(x) ? x.str() : name.at(x).symbol()->get();
      };
      os << "(= " << text(a) << " " << text(b) << ")";
    } else {
      Term shallow = subst.empty() ? u : tm.substitute_term(u, subst);
      os << bitwuzla::set_letify(false) << shallow;
    }
    lets += "(let ((" + kname + " " + os.str() + ")) ";
    closing += ")";
    name.emplace(u, tm.mk_const(u.sort(), kname));
  }
  if (leaf(t))
    return t.str();
  return lets + name.at(t).symbol()->get() + closing;
}

EncodingCheck checkBitwuzlaEncoding(Expr e, const bitwuzla::Term &t,
                                    unsigned timeout_ms,
                                    bitwuzla::TermManager *tm) {
  using V = EncodingVerdict;
  try {
    // -- the free constants of t, with their names and sorts; and the
    // -- variables, which binders in t must bind
    std::vector<SmtLibConst> consts;
    std::unordered_set<bitwuzla::Term> seen, vars, bound;
    std::unordered_set<std::string> varNames;
    bool binders = false, quantified = false;
    std::vector<bitwuzla::Term> todo{t};
    while (!todo.empty()) {
      bitwuzla::Term u = todo.back();
      todo.pop_back();
      if (!seen.insert(u).second)
        continue;
      if (u.is_variable()) {
        auto name = u.symbol();
        if (!name)
          return {V::UNCHECKED, "a variable has no name: " + u.str()};
        if (const char *why = unsafeName(name->get()))
          return {V::UNCHECKED,
                  "the name of variable " + name->get() + " " + why};
        vars.insert(u);
        // -- printed, two variables of one name could be read as one
        if (!varNames.insert(name->get()).second)
          return {V::UNCHECKED, "two variables are named " + name->get()};
      }
      if (u.kind() == bitwuzla::Kind::FORALL ||
          u.kind() == bitwuzla::Kind::EXISTS)
        quantified = true;
      if (isBinder(u)) {
        binders = true;
        for (size_t i = 0, n = u.num_children(); i + 1 < n; ++i)
          bound.insert(u[i]);
      }
      if (u.is_const()) {
        auto name = u.symbol();
        if (!name)
          return {V::UNCHECKED, "a constant has no name: " + u.str()};
        if (const char *why = unsafeName(name->get()))
          return {V::UNCHECKED,
                  "the name of constant " + name->get() + " " + why};
        bool ok;
        bitwuzla::Sort s = u.sort();
        unsigned index = 0;
        if (s.is_array()) {
          // -- an array from bit-vectors of width index to s
          index = widthOf(s.array_index(), ok);
          if (!ok || index == 0)
            return {V::UNCHECKED, "a constant of sort " + u.sort().str() +
                                      " is not supported by the check"};
          s = s.array_element();
        }
        unsigned w = widthOf(s, ok);
        if (!ok)
          return {V::UNCHECKED, "a constant of sort " + u.sort().str() +
                                    " is not supported by the check"};
        consts.push_back({name->get(), w, index});
      }
      for (const bitwuzla::Term &ch : u.children())
        todo.push_back(ch);
    }

    for (const bitwuzla::Term &v : vars)
      if (!bound.count(v))
        return {V::UNCHECKED, "the term has a free variable: " + v.str()};
    // -- printed, a variable named like a constant would hide it
    for (const SmtLibConst &k : consts)
      if (varNames.count(k.name))
        return {V::UNCHECKED,
                "a bound variable has the name of constant " + k.name};

    bool ok;
    unsigned w = widthOf(t.sort(), ok);
    if (!ok)
      return {V::UNCHECKED, "a term of sort " + t.sort().str() +
                                " is not supported by the check"};
    // -- printed by Bitwuzla, in SMT-LIB with let for shared subterms
    if (!binders)
      return checkSmtLibTermWithZ3(e, t.str(), consts, w, timeout_ms);
    // -- Bitwuzla's own printer gets let scopes wrong under binders
    if (!tm)
      return {V::UNCHECKED, "a term with binders needs its TermManager"};
    return checkSmtLibTermWithZ3(e, printWithLets(t, *tm), consts, w,
                                 timeout_ms, quantified);
  } catch (std::exception &ex) {
    return {V::UNCHECKED, std::string("Bitwuzla failed: ") + ex.what()};
  }
}

} // namespace solver
} // namespace seahorn

#endif
