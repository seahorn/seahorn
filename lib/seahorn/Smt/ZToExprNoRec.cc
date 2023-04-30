#include "seahorn/Expr/Smt/EZ3.hh"
#include "seahorn/Expr/Smt/ExprToZ.hh"

#include "seahorn/Expr/Smt/Z3.hh"

namespace seahorn {
template <typename C> class Unmarshaler {

  struct Frame {
    const z3::ast m_z;
    unsigned m_idx;

    Frame(const z3::ast &z, unsigned idx) : m_z(z), m_idx(idx) {}
    Frame(z3::context &ctx, const Z3_ast z_ast, unsigned idx)
        : m_z(ctx, z_ast), m_idx(idx) {}
  };

  expr::ExprFactory &m_efac;
  C &m_cache;
  seahorn::ast_expr_map &m_visited;

  llvm::SmallVector<Frame, 16> m_todoStack;
  llvm::SmallVector<Expr, 16> m_resStack;

public:
  Unmarshaler(expr::ExprFactory &efac, C &cache, seahorn::ast_expr_map &visited)
      : m_efac(efac), m_cache(cache), m_visited(visited) {}

private:
  bool visit(z3::context &ctx, const Z3_ast z) {
    return visit(z3::ast(ctx, z));
  }
  bool visit(z3::context &ctx, const Z3_sort z) {
    return visit(ctx, Z3_sort_to_ast(ctx, z));
  }

#define RETURN(X)                                                              \
  do {                                                                         \
    m_resStack.emplace_back(X);                                                \
    return true;                                                               \
  } while (0)

  bool visit(const z3::ast &z) {
    assert(z);
    using namespace expr;
    z3::context &ctx = z.ctx();

    Z3_lbool bVal = Z3_get_bool_value(ctx, z);
    if (bVal == Z3_L_TRUE) {
      RETURN(mk<TRUE>(m_efac));
    } else if (bVal == Z3_L_FALSE) {
      RETURN(mk<FALSE>(m_efac));
    }

    Z3_ast_kind kind = z.kind();

    switch (kind) {
    case Z3_SORT_AST: {
      Z3_sort sort = reinterpret_cast<Z3_sort>(static_cast<Z3_ast>(z));

      switch (Z3_get_sort_kind(ctx, sort)) {
      case Z3_BOOL_SORT:
        RETURN(sort::boolTy(m_efac));
      case Z3_INT_SORT:
        RETURN(sort::intTy(m_efac));
      case Z3_REAL_SORT:
        RETURN(sort::realTy(m_efac));
      case Z3_BV_SORT:
      case Z3_ARRAY_SORT:
        // needs caching, handled below
        break;
      default:
        assert(0 && "Unsupported sort");
      }
      break;
    }
    case Z3_VAR_AST:
    case Z3_APP_AST:
    case Z3_NUMERAL_AST:
    case Z3_QUANTIFIER_AST:
      // nothing
      break;
    case Z3_FUNC_DECL_AST: {
      auto it = m_cache.find(z);
      if (it != m_cache.end()) {
        RETURN(it->second);
      }
      break;
    }
    case Z3_UNKNOWN_AST:
      assert(false && "Unexpected");
      llvm_unreachable("unexpected");
    }

    // check cache
    if (shouldCache(z)) {
      auto it = m_cache.find(z);
      if (it != m_cache.end()) {
        RETURN(it->second);
      }
    }

    // check seen
    {
      auto it = m_visited.find(z);
      if (it != m_visited.end()) {
        RETURN(it->second);
      }
    }

    Expr res;
    switch (kind) {
    case Z3_NUMERAL_AST: {
      Z3_sort sort = Z3_get_sort(ctx, z);
      std::string snum = Z3_get_numeral_string(ctx, z);
      switch (Z3_get_sort_kind(ctx, sort)) {
      case Z3_REAL_SORT:
        res = mkTerm(mpq_class(snum), m_efac);
        break;
      case Z3_INT_SORT:
        res = mkTerm<expr::mpz_class>(expr::mpz_class(snum), m_efac);
        break;
      case Z3_BV_SORT:
        res = bv::bvnum(expr::mpz_class(snum), Z3_get_bv_sort_size(ctx, sort),
                        m_efac);
        break;
      default:
        assert(0 && "Unsupported numeric constant");
      }

      assert(res);
      assert(shouldCache(z));
      m_cache.insert({z, res});
      RETURN(res);
    }
    case Z3_SORT_AST: {
      Z3_sort sort = reinterpret_cast<Z3_sort>(static_cast<Z3_ast>(z));
      switch (Z3_get_sort_kind(ctx, sort)) {
      case Z3_BV_SORT:
        res = bv::bvsort(Z3_get_bv_sort_size(ctx, sort), m_efac);
        assert(shouldCache(z));
        m_cache.insert({z, res});
        RETURN(res);
      case Z3_ARRAY_SORT:
        break;
      default:
        assert(0 && "Unsupported sort");
        RETURN(Expr());
      }
      break;
    }
    case Z3_APP_AST:
    case Z3_QUANTIFIER_AST:
    case Z3_VAR_AST:
    case Z3_FUNC_DECL_AST:
      break;

    case Z3_UNKNOWN_AST:
      llvm_unreachable("impossible");
    }

    // could not process in one step, add to todo
    m_todoStack.emplace_back(z, 0);
    return false;
  }

  bool shouldCache(const z3::ast &z) {
    z3::context &ctx = z.ctx();
    switch (z.kind()) {
    case Z3_SORT_AST: {
      Z3_sort sort = reinterpret_cast<Z3_sort>(static_cast<Z3_ast>(z));
      switch (Z3_get_sort_kind(ctx, sort)) {
      case Z3_ARRAY_SORT:
      case Z3_BV_SORT:
      case Z3_UNINTERPRETED_SORT:
      case Z3_DATATYPE_SORT:
      case Z3_RELATION_SORT:
      case Z3_FLOATING_POINT_SORT:
      case Z3_FINITE_DOMAIN_SORT:
      case Z3_ROUNDING_MODE_SORT:
      case Z3_SEQ_SORT:
      case Z3_RE_SORT:
        return true;
      case Z3_BOOL_SORT:
      case Z3_INT_SORT:
      case Z3_REAL_SORT:
        return false;
      case Z3_UNKNOWN_SORT:
        llvm_unreachable("impossible");
      default:
        // case Z3_CHAR_SORT:
        llvm_unreachable("impossible");
      }
    }
    case Z3_NUMERAL_AST:
      return true;
    case Z3_APP_AST: {
      Z3_decl_kind dkind =
          Z3_get_decl_kind(ctx, Z3_get_app_decl(ctx, Z3_to_app(ctx, z)));
      switch (dkind) {
      case Z3_OP_UNINTERPRETED:
        return true;
      default:
        return false;
      }
    }
    default:
      return false;
    }
  }

#define VISIT(ZTERM)                                                           \
  if (!visit(ctx, ZTERM)) {                                                    \
    return;                                                                    \
  }

  void processTopFrame() {
    auto &frame = m_todoStack.back();
    const z3::ast &z = frame.m_z;
    z3::context &ctx = z.ctx();
    Z3_ast_kind kind = z.kind();
    unsigned arity = 0;

    switch (kind) {
    case Z3_SORT_AST: {
      Z3_sort sort = reinterpret_cast<Z3_sort>(static_cast<Z3_ast>(z));
      switch (Z3_get_sort_kind(ctx, sort)) {
      case Z3_ARRAY_SORT:
        arity = 2;
        while (frame.m_idx < arity) {
          auto idx = frame.m_idx++;
          switch (idx) {
          case 0:
            VISIT(Z3_get_array_sort_domain(ctx, sort));
            break;
          case 1:
            VISIT(Z3_get_array_sort_range(ctx, sort));
            break;
          default:
            llvm_unreachable("unexpected");
          }
        }
        break;
      default:
        assert(0 && "Unexpected sort");
        return;
      }
      break;
    }
    case Z3_VAR_AST:
      arity = 1;
      while (frame.m_idx < arity) {
        frame.m_idx++;
        VISIT(Z3_get_sort(ctx, z));
      }
      break;
    case Z3_QUANTIFIER_AST: {
      unsigned num_bound = Z3_get_quantifier_num_bound(ctx, z);
      arity = num_bound + 1;
      while (frame.m_idx < arity) {
        auto idx = frame.m_idx++;
        if (idx == num_bound) {
          VISIT(Z3_get_quantifier_body(ctx, z));
        } else {
          Z3_func_decl decl = Z3_mk_func_decl(
              ctx, Z3_get_quantifier_bound_name(ctx, z, idx), 0, nullptr,
              Z3_get_quantifier_bound_sort(ctx, z, idx));
          VISIT(Z3_func_decl_to_ast(ctx, decl));
        }
      }
      break;
    }
    case Z3_FUNC_DECL_AST: {
      Z3_func_decl fdecl = Z3_to_func_decl(ctx, z);
      unsigned domain_sz = Z3_get_domain_size(ctx, fdecl);
      arity = domain_sz + 1;

      while (frame.m_idx < arity) {
        auto idx = frame.m_idx++;
        if (idx == domain_sz) {
          VISIT(Z3_get_range(ctx, fdecl));
        } else {
          VISIT(Z3_get_domain(ctx, fdecl, idx));
        }
      }
      break;
    }
    case Z3_APP_AST: {
      Z3_app app = Z3_to_app(ctx, z);
      Z3_func_decl fdecl = Z3_get_app_decl(ctx, app);
      Z3_decl_kind dkind = Z3_get_decl_kind(ctx, fdecl);

      switch (dkind) {
      case Z3_OP_AS_ARRAY:
        arity = 1;
        while (frame.m_idx < arity) {
          frame.m_idx++;
          VISIT(Z3_func_decl_to_ast(ctx, Z3_get_as_array_func_decl(ctx, z)));
        }
        break;
      case Z3_OP_UNINTERPRETED: {
        arity = Z3_get_app_num_args(ctx, app) + 1;
        while (frame.m_idx < arity) {
          auto idx = frame.m_idx++;
          if (idx == 0) {
            VISIT(Z3_func_decl_to_ast(ctx, fdecl));
          } else {
            VISIT(Z3_get_app_arg(ctx, app, idx - 1));
          }
        }
        break;
      }
      case Z3_OP_CONST_ARRAY: {
        arity = Z3_get_app_num_args(ctx, app) + 1;
        while (frame.m_idx < arity) {
          auto idx = frame.m_idx++;
          if (idx == 0) {
            VISIT(Z3_get_sort(ctx, z));
          } else {
            VISIT(Z3_get_app_arg(ctx, app, idx - 1));
          }
        }
        break;
      }
      default: {
        arity = Z3_get_app_num_args(ctx, app);
        while (frame.m_idx < arity) {
          VISIT(Z3_get_app_arg(ctx, app, frame.m_idx++));
        }
      }
      }
      break;
    }
    default:
      assert(0 && "Unexpected Z3_ast_kind");
      return;
    }

    size_t kids_begin_idx = m_resStack.size() - arity;
    auto kids_it = m_resStack.begin() + kids_begin_idx;
    auto kids_it_end = m_resStack.end();

    Expr res;
    switch (kind) {
    case Z3_SORT_AST: {
      Z3_sort sort = reinterpret_cast<Z3_sort>(static_cast<Z3_ast>(z));
      switch (Z3_get_sort_kind(ctx, sort)) {
      case Z3_ARRAY_SORT: {
        auto &domain = *(kids_it++);
        auto &range = *(kids_it++);
        res = sort::arrayTy(domain, range);
        assert(shouldCache(z));
        m_cache.insert({z, res});
        break;
      }
      default:
        llvm_unreachable("unexpected");
      }
      break;
    }
    case Z3_VAR_AST: {
      auto &sort = *(kids_it++);
      unsigned idx = Z3_get_index_value(ctx, z);
      res = bind::bvar(idx, sort);
      break;
    }
    case Z3_QUANTIFIER_AST: {
      SmallVector<Expr, 32> args;
      unsigned num_bound = Z3_get_quantifier_num_bound(ctx, z);
      args.reserve(num_bound + 1);
      for (unsigned i = 0; i < num_bound; ++i) {
        args.emplace_back(*(kids_it++));
        assert(args.back().get());
      }
      args.push_back(*(kids_it)++);

      if (Z3_is_quantifier_forall(ctx, z))
        res = mknary<FORALL>(args);
      else if (Z3_is_quantifier_exists(ctx, z))
        res = mknary<EXISTS>(args);
      else {
        assert(Z3_is_lambda(ctx, z));
        res = mknary<LAMBDA>(args);
      }
      break;
    }
    case Z3_FUNC_DECL_AST: {
      Z3_func_decl fdecl = Z3_to_func_decl(ctx, z);
      Z3_symbol symname = Z3_get_decl_name(ctx, fdecl);

      Expr name;
      switch (Z3_get_symbol_kind(ctx, symname)) {
      case Z3_STRING_SYMBOL:
        name = mkTerm<std::string>(Z3_get_symbol_string(ctx, symname), m_efac);
        break;
      case Z3_INT_SYMBOL:
        name = mkTerm<expr::mpz_class>(
            (signed long)Z3_get_symbol_int(ctx, symname), m_efac);
        break;
      }
      assert(name);

      SmallVector<Expr, 8> type;
      for (unsigned p = 0; p < Z3_get_domain_size(ctx, fdecl); ++p) {
        type.push_back(*(kids_it)++);
      }
      type.push_back(*(kids_it)++);
      res = bind::fdecl(name, type);
      break;
    }
    case Z3_APP_AST: {
      Z3_app app;
      Z3_func_decl fdecl;
      Z3_decl_kind dkind;

      app = Z3_to_app(ctx, z);
      fdecl = Z3_get_app_decl(ctx, app);
      dkind = Z3_get_decl_kind(ctx, fdecl);

      switch (dkind) {
      case Z3_OP_NOT:
        res = mk<NEG>(*(kids_it++));
        break;
      case Z3_OP_UMINUS:
        res = mk<UN_MINUS>(*(kids_it++));
        break;
      case Z3_OP_TO_REAL:
      case Z3_OP_TO_INT:
        // XXX ignore to_real and to_int operators
        res = *(kids_it++);
        break;
      case Z3_OP_BNOT:
        res = mk<BNOT>(*(kids_it++));
        break;
      case Z3_OP_BNEG:
        res = mk<BNEG>(*(kids_it++));
        break;
      case Z3_OP_BREDAND:
        res = mk<BREDAND>(*(kids_it++));
        break;
      case Z3_OP_BREDOR:
        res = mk<BREDOR>(*(kids_it++));
        break;
      case Z3_OP_SIGN_EXT: {
        Expr sort =
            bv::bvsort(Z3_get_bv_sort_size(ctx, Z3_get_sort(ctx, z)), m_efac);
        res = mk<BSEXT>(*(kids_it++), sort);
        break;
      }
      case Z3_OP_ZERO_EXT: {
        Expr sort =
            bv::bvsort(Z3_get_bv_sort_size(ctx, Z3_get_sort(ctx, z)), m_efac);
        res = mk<BZEXT>(*(kids_it++), sort);
        break;
      }
      case Z3_OP_AS_ARRAY:
        res = mk<AS_ARRAY>(*(kids_it++));
        break;
      case Z3_OP_EXTRACT: {
        auto &arg = *(kids_it++);

        Z3_func_decl d = Z3_get_app_decl(ctx, app);
        unsigned high = Z3_get_decl_int_parameter(ctx, d, 0);
        unsigned low = Z3_get_decl_int_parameter(ctx, d, 1);
        res = bv::extract(high, low, arg);
        m_visited.insert({z, res});
        break;
      }
      case Z3_OP_UNINTERPRETED: {
        auto &fdecl = *(kids_it++);

        SmallVector<Expr, 32> args;
        for (unsigned i = 1; i < arity; ++i) {
          args.emplace_back(*(kids_it++));
        }
        res = bind::fapp(fdecl, args);
        break;
      }
      case Z3_OP_ITE:
        res = mknary<ITE>(kids_it, kids_it_end);
        break;
      case Z3_OP_AND:
        res = mknary<AND>(kids_it, kids_it_end);
        break;
      case Z3_OP_OR:
        res = mknary<OR>(kids_it, kids_it_end);
        break;
      case Z3_OP_XOR:
        res = mknary<XOR>(kids_it, kids_it_end);
        break;
      case Z3_OP_IFF:
        res = mknary<IFF>(kids_it, kids_it_end);
        break;
      case Z3_OP_IMPLIES:
        res = mknary<IMPL>(kids_it, kids_it_end);
        break;
      case Z3_OP_EQ:
        res = mknary<EQ>(kids_it, kids_it_end);
        break;
      case Z3_OP_LT:
        res = mknary<LT>(kids_it, kids_it_end);
        break;
      case Z3_OP_GT:
        res = mknary<GT>(kids_it, kids_it_end);
        break;
      case Z3_OP_LE:
        res = mknary<LEQ>(kids_it, kids_it_end);
        break;
      case Z3_OP_GE:
        res = mknary<GEQ>(kids_it, kids_it_end);
        break;
      case Z3_OP_ADD:
        res = mknary<PLUS>(kids_it, kids_it_end);
        break;
      case Z3_OP_SUB:
        res = mknary<MINUS>(kids_it, kids_it_end);
        break;
      case Z3_OP_MUL:
        res = mknary<MULT>(kids_it, kids_it_end);
        break;
      case Z3_OP_DIV:
        res = mknary<DIV>(kids_it, kids_it_end);
        break;
      case Z3_OP_IDIV:
        res = mknary<IDIV>(kids_it, kids_it_end);
        break;
      case Z3_OP_MOD:
        res = mknary<MOD>(kids_it, kids_it_end);
        break;
      case Z3_OP_REM:
        res = mknary<REM>(kids_it, kids_it_end);
        break;
      case Z3_OP_CONST_ARRAY: {
        auto &sort = *(kids_it++);
        auto &val = *(kids_it++);
        // Expr const-array take domain sort as first arg
        // Z3/SMT-LIB const-array take array sort as first arg
        res = op::array::constArray(sort->arg(0), val);
        break;
      }
      case Z3_OP_STORE:
        res = mknary<STORE>(kids_it, kids_it_end);
        break;
      case Z3_OP_SELECT:
        res = mknary<SELECT>(kids_it, kids_it_end);
        break;
      case Z3_OP_BADD:
        res = mknary<BADD>(kids_it, kids_it_end);
        break;
      case Z3_OP_BSUB:
        res = mknary<BSUB>(kids_it, kids_it_end);
        break;
      case Z3_OP_BMUL:
        res = mknary<BMUL>(kids_it, kids_it_end);
        break;
      case Z3_OP_BSMUL_NO_OVFL:
        res = mknary<SMUL_NO_OVERFLOW>(kids_it, kids_it_end);
        break;
      case Z3_OP_BUMUL_NO_OVFL:
        res = mknary<UMUL_NO_OVERFLOW>(kids_it, kids_it_end);
        break;
      case Z3_OP_BSMUL_NO_UDFL:
        res = mknary<SMUL_NO_UNDERFLOW>(kids_it, kids_it_end);
        break;
      case Z3_OP_BSDIV:
      case Z3_OP_BSDIV_I:
        res = mknary<BSDIV>(kids_it, kids_it_end);
        break;
      case Z3_OP_BUDIV:
      case Z3_OP_BUDIV_I:
        res = mknary<BUDIV>(kids_it, kids_it_end);
        break;
      case Z3_OP_BSREM:
      case Z3_OP_BSREM_I:
        res = mknary<BSREM>(kids_it, kids_it_end);
        break;
      case Z3_OP_BUREM:
      case Z3_OP_BUREM_I:
        res = mknary<BUREM>(kids_it, kids_it_end);
        break;
      case Z3_OP_BSMOD:
      case Z3_OP_BSMOD_I:
        res = mknary<BSMOD>(kids_it, kids_it_end);
        break;
      case Z3_OP_ULEQ:
        res = mknary<BULE>(kids_it, kids_it_end);
        break;
      case Z3_OP_SLEQ:
        res = mknary<BSLE>(kids_it, kids_it_end);
        break;
      case Z3_OP_UGEQ:
        res = mknary<BUGE>(kids_it, kids_it_end);
        break;
      case Z3_OP_SGEQ:
        res = mknary<BSGE>(kids_it, kids_it_end);
        break;
      case Z3_OP_ULT:
        res = mknary<BULT>(kids_it, kids_it_end);
        break;
      case Z3_OP_SLT:
        res = mknary<BSLT>(kids_it, kids_it_end);
        break;
      case Z3_OP_UGT:
        res = mknary<BUGT>(kids_it, kids_it_end);
        break;
      case Z3_OP_SGT:
        res = mknary<BSGT>(kids_it, kids_it_end);
        break;
      case Z3_OP_BAND:
        res = mknary<BAND>(kids_it, kids_it_end);
        break;
      case Z3_OP_BOR:
        res = mknary<BOR>(kids_it, kids_it_end);
        break;
      case Z3_OP_BXOR:
        res = mknary<BXOR>(kids_it, kids_it_end);
        break;
      case Z3_OP_BNAND:
        res = mknary<BNAND>(kids_it, kids_it_end);
        break;
      case Z3_OP_BNOR:
        res = mknary<BNOR>(kids_it, kids_it_end);
        break;
      case Z3_OP_BXNOR:
        res = mknary<BXNOR>(kids_it, kids_it_end);
        break;
      case Z3_OP_BSHL:
        res = mknary<BSHL>(kids_it, kids_it_end);
        break;
      case Z3_OP_BLSHR:
        res = mknary<BLSHR>(kids_it, kids_it_end);
        break;
      case Z3_OP_BASHR:
        res = mknary<BASHR>(kids_it, kids_it_end);
        break;
      case Z3_OP_CONCAT:
        res = mknary<BCONCAT>(kids_it, kids_it_end);
        break;
      default:
        res = Expr();
        ERR << "unknown expression: " << z.to_string() << "\n";
        llvm_unreachable("unknown z3 expression");
      }
      break;
    }
    default:
      res = Expr();
      ERR << "unknown expression: " << z.to_string() << "\n";
      llvm_unreachable("unknown z3 expression");
      assert(0);
    }

    m_visited.insert({z, res});
    m_resStack.resize(kids_begin_idx);
    m_resStack.emplace_back(std::move(res));
    m_todoStack.pop_back();
  }

public:
  expr::Expr operator()(const z3::ast &z) { return unmarshal(z); }

  expr::Expr unmarshal(const z3::ast &z) {

    if (visit(z))
      return m_resStack.back();

    while (!m_todoStack.empty()) {
      processTopFrame();
    }

    if (m_resStack.empty()) {
      ERR << "Failed to unmarshal:\n" << z.to_string() << "\n";
      llvm_unreachable("unexpected");
    }
    return m_resStack.back();
  }
};

template <typename C>
expr::Expr unmarshal_norec(const z3::ast &z, expr::ExprFactory &efac, C &cache,
                           seahorn::ast_expr_map &visited) {
  Unmarshaler<C> u(efac, cache, visited);
  return u(z);
}

template <typename C>
expr::Expr ZToExprNoRec::unmarshal(const z3::ast &z, expr::ExprFactory &efac,
                                   C &cache, ast_expr_map &seen) {
  return unmarshal_norec(z, efac, cache, seen);
}
} // namespace seahorn

namespace seahorn {
template expr::Expr ZToExprNoRec::unmarshal<typename EZ3::z_cache_type>(
    const z3::ast &, expr::ExprFactory &, typename EZ3::z_cache_type &,
    ast_expr_map &);
}
