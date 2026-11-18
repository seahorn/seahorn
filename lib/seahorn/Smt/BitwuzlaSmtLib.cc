#ifdef WITH_BITWUZLA

#include "seahorn/Expr/Smt/BitwuzlaSmtLib.hh"

#include <algorithm>
#include <cctype>
#include <set>
#include <sstream>
#include <stdexcept>
#include <unordered_map>
#include <unordered_set>
#include <utility>

namespace seahorn {
namespace solver {

using bitwuzla::Kind;
using bitwuzla::Term;

static bool isBinder(const Term &u) {
  return u.kind() == Kind::LAMBDA || u.kind() == Kind::FORALL ||
         u.kind() == Kind::EXISTS;
}

/// \p u with its children replaced by \p ch, or \p u itself if none changed
static Term rebuild(bitwuzla::TermManager &tm, const Term &u,
                    const std::vector<Term> &ch) {
  bool same = true;
  for (size_t i = 0, n = ch.size(); i < n && same; ++i)
    same = ch[i] == u[i];
  if (same)
    return u;
  // -- every other kind is rebuilt by mk_term from its kind, children and
  // -- indices (probe18d)
  if (u.kind() == Kind::CONST_ARRAY)
    return tm.mk_const_array(u.sort(), ch[0]);
  return tm.mk_term(u.kind(), ch, u.indices());
}

namespace {
/// Beta-reduction with the free variables of each term remembered
class BetaReducer {
  bitwuzla::TermManager &m_tm;
  /// the free variables of each term met so far
  std::unordered_map<Term, std::vector<Term>> m_fv;
  /// the reduced form of each term
  std::unordered_map<Term, Term> m_done;
  /// for an application of a lambda: the body with the arguments in place,
  /// whose reduced form is the application's
  std::unordered_map<Term, Term> m_redirect;

public:
  explicit BetaReducer(bitwuzla::TermManager &tm) : m_tm(tm) {}

  const std::vector<Term> &freeVars(const Term &t) {
    auto found = m_fv.find(t);
    if (found != m_fv.end())
      return found->second;
    std::vector<std::pair<Term, bool>> todo{{t, false}};
    while (!todo.empty()) {
      auto [u, expanded] = todo.back();
      if (m_fv.count(u)) {
        todo.pop_back();
        continue;
      }
      if (!expanded) {
        todo.back().second = true;
        for (const Term &c : u.children())
          if (!m_fv.count(c))
            todo.push_back({c, false});
        continue;
      }
      todo.pop_back();
      std::vector<Term> vs;
      if (u.is_variable())
        vs.push_back(u);
      size_t n = u.num_children(), bound = isBinder(u) ? n - 1 : 0;
      for (size_t i = 0; i < n; ++i)
        for (const Term &v : m_fv.at(u[i]))
          if (std::find(vs.begin(), vs.end(), v) == vs.end())
            vs.push_back(v);
      for (size_t i = 0; i < bound; ++i)
        vs.erase(std::remove(vs.begin(), vs.end(), u[i]), vs.end());
      m_fv.emplace(u, std::move(vs));
    }
    return m_fv.at(t);
  }

  /// \p x with each variable that is a key of \p map replaced by its value,
  /// only inside the subterms where one of them is free
  Term substitute(const Term &x, const std::unordered_map<Term, Term> &map) {
    auto relevant = [&](const Term &y) {
      for (const Term &v : freeVars(y))
        if (map.count(v))
          return true;
      return false;
    };
    std::unordered_map<Term, Term> res;
    std::vector<std::pair<Term, bool>> todo{{x, false}};
    while (!todo.empty()) {
      auto [y, expanded] = todo.back();
      if (res.count(y)) {
        todo.pop_back();
        continue;
      }
      if (!relevant(y)) {
        res.emplace(y, y);
        todo.pop_back();
        continue;
      }
      if (y.is_variable()) {
        res.emplace(y, map.at(y));
        todo.pop_back();
        continue;
      }
      if (!expanded) {
        // -- a binder that binds a variable being replaced, with another
        // -- one free in it: the encoder makes new variables for every
        // -- binder, so this does not happen; refuse rather than capture
        if (isBinder(y))
          for (size_t i = 0, n = y.num_children(); i + 1 < n; ++i)
            if (map.count(y[i]))
              throw std::runtime_error(
                  "beta-reduction: a binder binds a variable being replaced");
        todo.back().second = true;
        for (const Term &c : y.children())
          if (!res.count(c))
            todo.push_back({c, false});
        continue;
      }
      todo.pop_back();
      std::vector<Term> ch;
      for (const Term &c : y.children())
        ch.push_back(res.at(c));
      res.emplace(y, rebuild(m_tm, y, ch));
    }
    return res.at(x);
  }

  /// \p u applies a lambda of at least as many variables as it has
  /// arguments
  static bool isRedex(const Term &u) {
    if (u.kind() != Kind::APPLY)
      return false;
    Term f = u[0];
    for (size_t i = 1, n = u.num_children(); i < n; ++i) {
      if (f.kind() != Kind::LAMBDA)
        return false;
      f = f[1];
    }
    return true;
  }

  /// the body of the lambda that \p u applies, with its arguments in place
  /// of the variables
  Term instantiate(const Term &u) {
    std::unordered_map<Term, Term> map;
    Term f = u[0];
    for (size_t i = 1, n = u.num_children(); i < n; ++i) {
      map.emplace(f[0], u[i]);
      f = f[1];
    }
    return substitute(f, map);
  }

  Term reduce(const Term &t) {
    std::vector<Term> todo{t};
    while (!todo.empty()) {
      Term u = todo.back();
      if (m_done.count(u)) {
        todo.pop_back();
        continue;
      }
      if (u.num_children() == 0) {
        m_done.emplace(u, u);
        todo.pop_back();
        continue;
      }
      if (isRedex(u)) {
        // -- the arguments go into the lambda's body as it is; what that
        // -- gives is then reduced like any term
        auto r = m_redirect.find(u);
        if (r == m_redirect.end()) {
          Term body = instantiate(u);
          m_redirect.emplace(u, body);
          todo.push_back(body);
          continue;
        }
        m_done.emplace(u, m_done.at(r->second));
        todo.pop_back();
        continue;
      }
      bool ready = true;
      for (const Term &c : u.children())
        if (!m_done.count(c)) {
          todo.push_back(c);
          ready = false;
        }
      if (!ready)
        continue;
      todo.pop_back();
      std::vector<Term> ch;
      for (const Term &c : u.children())
        ch.push_back(m_done.at(c));
      m_done.emplace(u, rebuild(m_tm, u, ch));
    }
    return m_done.at(t);
  }
};
} // namespace

std::vector<Term> betaReduce(bitwuzla::TermManager &tm,
                             const std::vector<Term> &terms) {
  BetaReducer r(tm);
  std::vector<Term> out;
  for (const Term &t : terms)
    out.push_back(r.reduce(t));
  return out;
}

/// The names Bitwuzla 0.9.1's parser takes as its own: every token of its
/// symbol table (src/parser/smt2/token.cpp: reserved words, commands,
/// keywords, sorts, and the symbols of the theories, floating-point ones
/// too, which (set-logic ALL) turns on). A constant of such a name cannot
/// be declared, quoted or not: its symbol table reads |x| as x. z3 accepts
/// them all.
static const std::set<std::string> &reservedNames() {
  static const std::set<std::string> names = {
      "(", ")", "!", "_", "as", "BINARY", "DECIMAL", "exists", "forall",
      "HEXADECIMAL", "let", "NUMERAL", "par", "STRING",
      // -- SMT-LIB's other reserved words, and lambda (2.7)
      "match", "lambda",
      // -- commands
      "assert", "check-sat", "check-sat-assuming", "declare-const",
      "declare-fun", "declare-sort", "define-const", "define-fun",
      "define-sort", "echo", "exit", "get-assertions", "get-assignment",
      "get-info", "get-interpolant", "get-interpolants", "get-option",
      "get-model", "get-proof", "get-unsat-assumptions", "get-unsat-core",
      "get-value", "pop", "push", "reset", "reset-assertions", "set-logic",
      "set-info", "set-option",
      // -- keywords
      ":all-statistics", ":assertion-stack-levels", ":authors", ":category",
      ":chainable", ":definition", ":diagnostic-output-channel",
      ":error-behavior", ":extensions", ":funs", ":funs-description",
      ":interactive-mode", ":language", ":left-assoc", ":license", ":name",
      ":named", ":notes", ":pattern", ":print-success", ":produce-assignments",
      ":produce-models", ":produce-proofs", ":produce-unsat-assumptions",
      ":produce-unsat-cores", ":random-seed", ":reason-unknown",
      ":regular-output-channel", ":reproducible-resource-limit", ":right-assoc",
      ":smt-lib-version", ":sorts", ":sorts-description", ":status", ":source",
      ":theories", ":values", ":verbosity", ":version", ":global-declarations",
      // -- Core
      "and", "Bool", "distinct", "=", "false", "=>", "ite", "not", "or", "true",
      "xor",
      // -- arrays
      "Array", "select", "store", "const",
      // -- bit-vectors
      "BitVec", "bvadd", "bvand", "bvashr", "bvcomp", "concat", "extract",
      "bvlshr", "bvmul", "bvnand", "bvneg", "bvnor", "bvnot", "bvor", "repeat",
      "bvrol", "bvror", "rotate_left", "rotate_right", "bvsdiv", "bvsge",
      "bvsgt", "bvshl", "sign_extend", "bvsle", "bvslt", "bvsmod", "bvsrem",
      "bvsub", "bvudiv", "bvuge", "bvugt", "bvule", "bvult", "bvurem", "bvxnor",
      "bvxor", "zero_extend", "bvdec", "bvinc", "bvredor", "bvredand",
      "bvredxor", "bvnego", "bvsaddo", "bvuaddo", "bvsdivo", "bvsmulo",
      "bvumulo", "bvssubo", "bvusubo",
      // -- floating-point
      "FloatingPoint", "Float16", "Float32", "Float64", "Float128",
      "RoundingMode", "RNA", "roundNearestTiesToAway", "RNE",
      "roundNearestTiesToEven", "RTN", "roundTowardNegative", "RTP",
      "roundTowardPositive", "RTZ", "roundTowardZero", "fp.abs", "fp.add",
      "fp.div", "fp.eq", "fp.fma", "fp", "fp.geq", "fp.gt", "fp.isInfinite",
      "fp.isNaN", "fp.isNegative", "fp.isNormal", "fp.isPositive",
      "fp.isSubnormal", "fp.isZero", "fp.leq", "fp.lt", "fp.max", "fp.min",
      "fp.mul", "NaN", "fp.neg", "-oo", "-zero", "+oo", "+zero", "fp.rem",
      "fp.roundToIntegral", "fp.sqrt", "fp.sub", "to_fp", "to_fp_unsigned",
      "fp.to_sbv", "fp.to_ubv", "/"};
  return names;
}

static bool startsWith(const std::string &s, const char *prefix) {
  return s.compare(0, std::char_traits<char>::length(prefix), prefix) == 0;
}

/// \p name prints, in Bitwuzla's printer, as a symbol that both parsers
/// read as itself
static bool printableName(const std::string &name) {
  if (name.empty())
    return false;
  // -- SMT-LIB cannot quote either; Bitwuzla throws on |
  if (name.find('|') != std::string::npos ||
      name.find('\\') != std::string::npos)
    return false;
  // -- Bitwuzla prints a name of symbol characters as it is, and one that
  // -- starts with a digit then reads as a numeral or not at all
  if (std::isdigit(static_cast<unsigned char>(name[0])))
    return false;
  // -- Bitwuzla's own names: unnamed terms and lets
  if (startsWith(name, "@bzla.") || startsWith(name, "_let"))
    return false;
  return !reservedNames().count(name);
}

/// The constants and variables of \p terms, in the order a depth-first
/// walk meets them
static std::vector<Term> leavesToName(const std::vector<Term> &terms) {
  std::vector<Term> out;
  std::unordered_set<Term> seen;
  for (const Term &t : terms) {
    std::vector<Term> todo{t};
    while (!todo.empty()) {
      Term u = todo.back();
      todo.pop_back();
      if (!seen.insert(u).second)
        continue;
      if (u.is_const() || u.is_variable()) {
        out.push_back(u);
        continue;
      }
      std::vector<Term> ch = u.children();
      // -- children in order: the first child is met first
      todo.insert(todo.end(), ch.rbegin(), ch.rend());
    }
  }
  return out;
}

namespace {
/// Whether a term has a binder inside another binder's body
class NestedBinders {
  std::unordered_map<Term, bool> m_has_binder, m_nested;

  bool hasBinder(const Term &t) {
    std::vector<std::pair<Term, bool>> todo{{t, false}};
    while (!todo.empty()) {
      auto [u, expanded] = todo.back();
      if (m_has_binder.count(u)) {
        todo.pop_back();
        continue;
      }
      if (!expanded) {
        todo.back().second = true;
        for (const Term &c : u.children())
          if (!m_has_binder.count(c))
            todo.push_back({c, false});
        continue;
      }
      todo.pop_back();
      bool b = isBinder(u);
      for (const Term &c : u.children())
        b = b || m_has_binder.at(c);
      m_has_binder.emplace(u, b);
    }
    return m_has_binder.at(t);
  }

public:
  bool operator()(const Term &t) {
    std::unordered_set<Term> seen;
    std::vector<Term> todo{t};
    while (!todo.empty()) {
      Term u = todo.back();
      todo.pop_back();
      if (!seen.insert(u).second)
        continue;
      if (isBinder(u) && hasBinder(u[u.num_children() - 1]))
        return true;
      for (const Term &c : u.children())
        todo.push_back(c);
    }
    return false;
  }
};
} // namespace

std::string printSmtLib(bitwuzla::TermManager &tm,
                        const std::vector<Term> &assertions,
                        const std::vector<size_t> &levels, bool *lambda_left) {
  std::vector<Term> ts = betaReduce(tm, assertions);

  // -- rename what would not print as itself, and every name after its
  // -- first use, to a name used nowhere (not even by a later term)
  std::vector<Term> leaves = leavesToName(ts);
  std::unordered_set<std::string> original, used;
  for (const Term &u : leaves)
    if (auto s = u.symbol())
      original.insert(s->get());
  std::unordered_map<std::string, unsigned> next; // -- per base name
  auto fresh = [&](const std::string &base) {
    std::string name;
    for (unsigned &k = next[base];;) {
      name = base + "!" + std::to_string(++k);
      if (printableName(name) && !original.count(name) && !used.count(name))
        break;
    }
    used.insert(name);
    return name;
  };
  std::unordered_map<Term, Term> rename;
  for (const Term &u : leaves) {
    auto sym = u.symbol();
    std::string name = sym ? sym->get() : std::string();
    if (printableName(name) && used.insert(name).second)
      continue;
    std::string base = name;
    std::replace(base.begin(), base.end(), '|', '_');
    std::replace(base.begin(), base.end(), '\\', '_');
    if (base.empty() || std::isdigit(static_cast<unsigned char>(base[0])) ||
        startsWith(base, "@bzla.") || startsWith(base, "_let"))
      base = (u.is_variable() ? "v_" : "c_") + base;
    std::string n = fresh(base);
    rename.emplace(u, u.is_variable() ? tm.mk_var(u.sort(), n)
                                      : tm.mk_const(u.sort(), n));
  }
  if (!rename.empty())
    tm.substitute_terms(ts, rename); // -- in place

  // -- every term in post-order (children first), and how often each is
  // -- used: as an assertion, or as a child (twice by one parent counts
  // -- twice)
  std::vector<Term> order;
  std::unordered_map<Term, unsigned> uses;
  {
    std::unordered_set<Term> expanded, finished;
    std::vector<std::pair<Term, bool>> todo;
    for (size_t i = ts.size(); i-- > 0;) {
      ++uses[ts[i]];
      todo.push_back({ts[i], false});
    }
    while (!todo.empty()) {
      auto [u, post] = todo.back();
      todo.pop_back();
      if (post) {
        if (finished.insert(u).second)
          order.push_back(u);
        continue;
      }
      if (!expanded.insert(u).second)
        continue;
      todo.push_back({u, true});
      for (size_t i = u.num_children(); i-- > 0;) {
        ++uses[u[i]];
        todo.push_back({u[i], false});
      }
    }
  }

  // -- Every closed term that is not a leaf and is used twice or more gets a
  // -- definition at the top, children first; each definition and assertion
  // -- is printed over those names. So the text grows with the formula's
  // -- DAG, also inside binders. (Bitwuzla's own printer defines only terms
  // -- with two parents, outside binders, of two or more children, and
  // -- without lets prints every other copy in full: exponential growth,
  // -- found by the review of step 1.8.)
  BetaReducer fvs(tm);
  std::unordered_map<Term, Term> shallow, name;
  auto repr = [&](const Term &c) {
    auto it = name.find(c);
    return it != name.end() ? it->second : shallow.at(c);
  };
  // -- Bitwuzla's lets are left on: what is shared now is open, used only
  // -- in the body of its binder, where the let goes. They are off for a
  // -- term with a binder in a binder's body, where a let made in the inner
  // -- body could be used outside it (the printer bug of plan 1.7).
  NestedBinders nested;
  auto print = [&](const Term &t) {
    std::ostringstream os;
    os << bitwuzla::set_letify(!nested(t)) << t;
    return os.str();
  };
  std::ostringstream defs;
  for (const Term &u : order) {
    if (u.num_children() == 0) {
      shallow.emplace(u, u);
      continue;
    }
    std::vector<Term> ch;
    for (const Term &c : u.children())
      ch.push_back(repr(c));
    Term s = rebuild(tm, u, ch);
    shallow.emplace(u, s);
    if (uses.at(u) >= 2 && fvs.freeVars(u).empty()) {
      std::string n = fresh("def");
      name.emplace(u, tm.mk_const(u.sort(), n));
      defs << "(define-const " << n << " " << u.sort() << " " << print(s)
           << ")\n";
    }
  }

  bool lambda = false;
  for (const Term &u : order)
    lambda = lambda || u.kind() == Kind::LAMBDA;
  if (lambda_left)
    *lambda_left = lambda;

  // -- the logic is ALL: Bitwuzla 0.9.1's printer picks one from the sorts
  // -- of the terms with an else-if chain, so arrays of bit-vectors whose
  // -- bit-vectors are in no term gave QF_A, which its own parser rejects
  // -- (found by the fuzzer, 2026-11-18)
  std::ostringstream os;
  os << "(set-logic ALL)\n";
  for (const Term &u : leaves) {
    Term c = rename.count(u) ? rename.at(u) : u;
    if (!c.is_const())
      continue;
    bitwuzla::Sort s = c.sort();
    if (s.is_fun()) {
      os << "(declare-fun " << c << " (";
      const char *sep = "";
      for (const bitwuzla::Sort &d : s.fun_domain()) {
        os << sep << d;
        sep = " ";
      }
      os << ") " << s.fun_codomain() << ")\n";
    } else {
      os << "(declare-const " << c << " " << s << ")\n";
    }
  }
  os << defs.str();
  size_t level = 0;
  for (size_t i = 0, n = ts.size(); i < n; ++i) {
    for (; level < levels[i]; ++level)
      os << "(push 1)\n";
    os << "(assert " << print(repr(ts[i])) << ")\n";
  }
  os << "(check-sat)\n(exit)\n";
  return os.str();
}

} // namespace solver
} // namespace seahorn

#endif
