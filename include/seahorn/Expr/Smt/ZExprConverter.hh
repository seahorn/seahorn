#ifndef Z3_EXPR_CONVERTER__HPP_
#define Z3_EXPR_CONVERTER__HPP_

/** Marshal and Unmarshal between Z3 ast and Expr*/

// --  used for CL options
#include "seahorn/Expr/Smt/Z3.hh"
#include "seahorn/Expr/ExprLlvm.hh"

#include "llvm/Support/raw_ostream.h"

namespace ufo {

struct FailMarshal {
  template <typename C>
  static z3::ast marshal(Expr e, z3::context &ctx, C &cache,
                         expr_ast_map &seen) {
    llvm::errs() << "Cannot marshal: " << *e << "\n";
    assert(0);
    exit(1);
  }
};

struct FailUnmarshal {
  template <typename C>
  static Expr unmarshal(const z3::ast &a, ExprFactory &efac, C &cache,
                        ast_expr_map &seen) {
    llvm::errs() << "Cannot unmarshal: " << lexical_cast<std::string>(a)
                 << "\n";
    assert(0);
    exit(1);
  }
};

template <typename M> struct BasicExprMarshal {
  template <typename C>
  static z3::ast marshal(Expr e, z3::context &ctx, C &cache,
                         expr_ast_map &seen) {
    assert(e);
    if (isOpX<TRUE>(e))
      return z3::ast(ctx, Z3_mk_true(ctx));
    if (isOpX<FALSE>(e))
      return z3::ast(ctx, Z3_mk_false(ctx));

    /** check the cache */
    {
      typename C::const_iterator it = cache.find(e);
      if (it != cache.end())
        return it->second;
    }

    /** check computed table */
    {
      typename expr_ast_map::const_iterator it = seen.find(e);
      if (it != seen.end())
        return it->second;
    }

    Z3_ast res = nullptr;

    if (bind::isBVar(e)) {
      z3::ast sort(marshal(bind::type(e), ctx, cache, seen));
      res = Z3_mk_bound(ctx, bind::bvarId(e),
                        reinterpret_cast<Z3_sort>(static_cast<Z3_ast>(sort)));
    } else if (isOpX<INT_TY>(e))
      res = reinterpret_cast<Z3_ast>(Z3_mk_int_sort(ctx));
    else if (isOpX<REAL_TY>(e))
      res = reinterpret_cast<Z3_ast>(Z3_mk_real_sort(ctx));
    else if (isOpX<BOOL_TY>(e))
      res = reinterpret_cast<Z3_ast>(Z3_mk_bool_sort(ctx));
    else if (isOpX<ARRAY_TY>(e)) {
      z3::ast _idx_sort(marshal(e->left(), ctx, cache, seen));
      z3::ast _val_sort(marshal(e->right(), ctx, cache, seen));
      Z3_sort idx_sort =
          reinterpret_cast<Z3_sort>(static_cast<Z3_ast>(_idx_sort));
      Z3_sort val_sort =
          reinterpret_cast<Z3_sort>(static_cast<Z3_ast>(_val_sort));
      res = reinterpret_cast<Z3_ast>(Z3_mk_array_sort(ctx, idx_sort, val_sort));
    } else if (isOpX<BVSORT>(e))
      res = reinterpret_cast<Z3_ast>(Z3_mk_bv_sort(ctx, bv::width(e)));

    else if (isOpX<INT>(e)) {
      z3::sort sort(ctx, Z3_mk_real_sort(ctx));
      std::string sname = boost::lexical_cast<std::string>(e.get());
      res = Z3_mk_numeral(ctx, sname.c_str(), sort);
    }

    else if (isOpX<MPQ>(e)) {
      const mpq_class &val = getTerm<mpq_class>(e);
      z3::sort sort(ctx, Z3_mk_real_sort(ctx));
      std::string sname = boost::lexical_cast<std::string>(val);
      res = Z3_mk_numeral(ctx, sname.c_str(), sort);
    } else if (isOpX<MPZ>(e)) {
      const mpz_class &val = getTerm<mpz_class>(e);
      z3::sort sort(ctx, Z3_mk_int_sort(ctx));
      std::string sname = boost::lexical_cast<std::string>(val);
      res = Z3_mk_numeral(ctx, sname.c_str(), sort);
    } else if (bv::is_bvnum(e)) {
      z3::sort sort(ctx, Z3_mk_bv_sort(ctx, bv::width(e->arg(1))));
      const mpz_class &val = getTerm<mpz_class>(e->arg(0));
      std::string sname = boost::lexical_cast<std::string>(val);
      res = Z3_mk_numeral(ctx, sname.c_str(), sort);
    } else if (bind::isBoolVar(e)) {
      // XXX The name 'edge' is misleading. Should be changed.
      Expr edge = bind::name(e);
      std::string svar;
      // -- for variables with string names, use the names
      if (isOpX<STRING>(edge))
        svar = getTerm<std::string>(edge);
      else // -- for non-string named variables use address
        svar = "E" + boost::lexical_cast<std::string, void *>(edge.get());

      res = Z3_mk_const(ctx, ctx.str_symbol(svar.c_str()), ctx.bool_sort());
    } else if (bind::isIntVar(e)) {
      Expr name = bind::name(e);
      std::string sname;
      if (isOpX<STRING>(name))
        sname = getTerm<std::string>(name);
      else
        sname = "I" + lexical_cast<std::string, void *>(name.get());

      res = Z3_mk_const(ctx, ctx.str_symbol(sname.c_str()), ctx.int_sort());
    } else if (bind::isRealVar(e)) {
      Expr name = bind::name(e);
      std::string sname;
      if (isOpX<STRING>(name))
        sname = getTerm<std::string>(name);
      else
        sname = "R" + lexical_cast<std::string, void *>(name.get());

      res = Z3_mk_const(ctx, ctx.str_symbol(sname.c_str()), ctx.real_sort());
    }

    /** function declaration */
    else if (bind::isFdecl(e)) {
      z3::ast_vector pinned(ctx);
      pinned.resize(e->arity());
      std::vector<Z3_sort> domain(e->arity());

      for (size_t i = 0; i < bind::domainSz(e); ++i) {
        z3::ast a(marshal(bind::domainTy(e, i), ctx, cache, seen));
        pinned.push_back(a);
        domain[i] = reinterpret_cast<Z3_sort>(static_cast<Z3_ast>(a));
      }

      z3::sort range(ctx, reinterpret_cast<Z3_sort>(static_cast<Z3_ast>(
                              marshal(bind::rangeTy(e), ctx, cache, seen))));

      Expr fname = bind::fname(e);
      std::string sname;
      if (isOpX<STRING>(fname))
        sname = getTerm<std::string>(fname);
      else
        // sname = "F" + lexical_cast<std::string,void*>(fname.get ());
        sname = lexical_cast<std::string>(*fname);

      z3::symbol symname = ctx.str_symbol(sname.c_str());

      res = reinterpret_cast<Z3_ast>(
          Z3_mk_func_decl(ctx, symname, bind::domainSz(e), &domain[0], range));
    }

    /** function application */
    else if (bind::isFapp(e)) {

      z3::func_decl zfdecl(ctx,
                           reinterpret_cast<Z3_func_decl>(static_cast<Z3_ast>(
                               marshal(bind::fname(e), ctx, cache, seen))));

      // -- marshall all arguments except for the first one
      // -- (which is the fdecl)
      std::vector<Z3_ast> args(e->arity());
      z3::ast_vector pinned_args(ctx);
      pinned_args.resize(e->arity());

      unsigned pos = 0;
      for (ENode::args_iterator it = ++(e->args_begin()), end = e->args_end();
           it != end; ++it) {
        z3::ast a(marshal(*it, ctx, cache, seen));
        pinned_args.push_back(a);
        args[pos++] = a;
      }

      res = Z3_mk_app(ctx, zfdecl, e->arity() - 1, &args[0]);
    }
    /** quantifier */
    else if (isOpX<FORALL>(e) || isOpX<EXISTS>(e) || isOpX<LAMBDA>(e)) {
      unsigned num_bound = bind::numBound(e);
      z3::ast_vector pinned(ctx);
      pinned.resize(num_bound);
      std::vector<Z3_sort> bound_sorts;
      bound_sorts.reserve(num_bound);
      std::vector<Z3_symbol> bound_names;
      bound_names.reserve(num_bound);

      for (unsigned i = 0; i < num_bound; ++i) {
        z3::ast z(marshal(bind::decl(e, i), ctx, cache, seen));
        pinned.push_back(z);

        Z3_func_decl decl = Z3_to_func_decl(ctx, z);
        bound_sorts.push_back(Z3_get_range(ctx, decl));
        bound_names.push_back(Z3_get_decl_name(ctx, decl));
      }

      z3::ast body(marshal(bind::body(e), ctx, cache, seen));
      if (isOpX<FORALL>(e) || isOpX<EXISTS>(e)) {
        res = Z3_mk_quantifier(ctx, isOpX<FORALL>(e), 0, 0, nullptr, num_bound,
                               &bound_sorts[0], &bound_names[0], body);
      } else {
        assert(isOpX<LAMBDA>(e));
        res = Z3_mk_lambda(ctx, num_bound,
                           &bound_sorts[0], &bound_names[0], body);
      }
    }

    // -- cache the result for unmarshaling
    if (res) {
      z3::ast ast(ctx, res);
      cache.insert(typename C::value_type(e, ast));
      return ast;
    }

    int arity = e->arity();
    /** other terminal expressions */
    if (arity == 0)
      return M::marshal(e, ctx, cache, seen);

    else if (arity == 1) {
      // -- then it's a NEG or UN_MINUS
      if (isOpX<UN_MINUS>(e)) {
        z3::ast arg = marshal(e->left(), ctx, cache, seen);
        return z3::ast(ctx, Z3_mk_unary_minus(ctx, arg));
      }

      if (isOpX<NEG>(e)) {
        z3::ast arg = marshal(e->left(), ctx, cache, seen);
        return z3::ast(ctx, Z3_mk_not(ctx, arg));
      }
      if (isOpX<ARRAY_DEFAULT>(e)) {
        z3::ast arg = marshal(e->left(), ctx, cache, seen);
        return z3::ast(ctx, Z3_mk_array_default(ctx, arg));
      }
      if (isOpX<BNOT>(e)) {
        z3::ast arg = marshal(e->left(), ctx, cache, seen);
        return z3::ast(ctx, Z3_mk_bvnot(ctx, arg));
      }
      if (isOpX<BNEG>(e)) {
        z3::ast arg = marshal(e->left(), ctx, cache, seen);
        return z3::ast(ctx, Z3_mk_bvneg(ctx, arg));
      }
      if (isOpX<BREDAND>(e)) {
        z3::ast arg = marshal(e->left(), ctx, cache, seen);
        return z3::ast(ctx, Z3_mk_bvredand(ctx, arg));
      }
      if (isOpX<BREDOR>(e)) {
        z3::ast arg = marshal(e->left(), ctx, cache, seen);
        return z3::ast(ctx, Z3_mk_bvredor(ctx, arg));
      }

      return M::marshal(e, ctx, cache, seen);
    } else if (arity == 2) {
      z3::ast t1 = marshal(e->left(), ctx, cache, seen);
      z3::ast t2 = marshal(e->right(), ctx, cache, seen);

      Z3_ast args[2] = {t1, t2};

      /** BoolOp */
      if (isOpX<AND>(e))
        res = Z3_mk_and(ctx, 2, args);
      else if (isOpX<OR>(e))
        res = Z3_mk_or(ctx, 2, args);
      else if (isOpX<IMPL>(e))
        res = Z3_mk_implies(ctx, t1, t2);
      else if (isOpX<IFF>(e))
        res = Z3_mk_iff(ctx, t1, t2);
      else if (isOpX<XOR>(e))
        res = Z3_mk_xor(ctx, t1, t2);

      /** NumericOp */
      else if (isOpX<PLUS>(e))
        res = Z3_mk_add(ctx, 2, args);
      else if (isOpX<MINUS>(e))
        res = Z3_mk_sub(ctx, 2, args);
      else if (isOpX<MULT>(e))
        res = Z3_mk_mul(ctx, 2, args);
      else if (isOpX<DIV>(e) || isOpX<IDIV>(e))
        res = Z3_mk_div(ctx, t1, t2);
      else if (isOpX<MOD>(e))
        res = Z3_mk_mod(ctx, t1, t2);
      else if (isOpX<REM>(e))
        res = Z3_mk_rem(ctx, t1, t2);

      /** Comparison Op */
      else if (isOpX<EQ>(e))
        res = Z3_mk_eq(ctx, t1, t2);
      else if (isOpX<NEQ>(e))
        res = Z3_mk_not(ctx, Z3_mk_eq(ctx, t1, t2));
      else if (isOpX<LEQ>(e))
        res = Z3_mk_le(ctx, t1, t2);
      else if (isOpX<GEQ>(e))
        res = Z3_mk_ge(ctx, t1, t2);
      else if (isOpX<LT>(e))
        res = Z3_mk_lt(ctx, t1, t2);
      else if (isOpX<GT>(e))
        res = Z3_mk_gt(ctx, t1, t2);

      /** Array Select */
      else if (isOpX<SELECT>(e))
        res = Z3_mk_select(ctx, t1, t2);
      /** Array Const */
      else if (isOpX<CONST_ARRAY>(e)) {
        Z3_sort domain = reinterpret_cast<Z3_sort>(static_cast<Z3_ast>(t1));
        res = Z3_mk_const_array(ctx, domain, t2);
        assert(res);
      }

      /** Bit-Vectors */
      else if (isOpX<BSEXT>(e) || isOpX<BZEXT>(e)) {
        assert(Z3_get_sort_kind(ctx, Z3_get_sort(ctx, t1)) == Z3_BV_SORT);
        unsigned t1_sz = Z3_get_bv_sort_size(ctx, Z3_get_sort(ctx, t1));
        assert(t1_sz > 0);
        assert(t1_sz < bv::width(e->arg(1)));
        if (isOpX<BSEXT>(e))
          res = z3::ast(ctx,
                        Z3_mk_sign_ext(ctx, bv::width(e->arg(1)) - t1_sz, t1));
        else if (isOpX<BZEXT>(e))
          res = z3::ast(ctx,
                        Z3_mk_zero_ext(ctx, bv::width(e->arg(1)) - t1_sz, t1));
        else
          assert(0);
      } else if (isOpX<BAND>(e))
        res = Z3_mk_bvand(ctx, t1, t2);
      else if (isOpX<BOR>(e))
        res = Z3_mk_bvor(ctx, t1, t2);
      else if (isOpX<BMUL>(e))
        res = Z3_mk_bvmul(ctx, t1, t2);
      else if (isOpX<BADD>(e))
        res = Z3_mk_bvadd(ctx, t1, t2);
      else if (isOpX<BSUB>(e))
        res = Z3_mk_bvsub(ctx, t1, t2);
      else if (isOpX<BSDIV>(e))
        res = Z3_mk_bvsdiv(ctx, t1, t2);
      else if (isOpX<BUDIV>(e))
        res = Z3_mk_bvudiv(ctx, t1, t2);
      else if (isOpX<BSREM>(e))
        res = Z3_mk_bvsrem(ctx, t1, t2);
      else if (isOpX<BUREM>(e))
        res = Z3_mk_bvurem(ctx, t1, t2);
      else if (isOpX<BSMOD>(e))
        res = Z3_mk_bvsmod(ctx, t1, t2);
      else if (isOpX<BULE>(e))
        res = Z3_mk_bvule(ctx, t1, t2);
      else if (isOpX<BSLE>(e))
        res = Z3_mk_bvsle(ctx, t1, t2);
      else if (isOpX<BUGE>(e))
        res = Z3_mk_bvuge(ctx, t1, t2);
      else if (isOpX<BSGE>(e))
        res = Z3_mk_bvsge(ctx, t1, t2);
      else if (isOpX<BULT>(e))
        res = Z3_mk_bvult(ctx, t1, t2);
      else if (isOpX<BSLT>(e))
        res = Z3_mk_bvslt(ctx, t1, t2);
      else if (isOpX<BUGT>(e))
        res = Z3_mk_bvugt(ctx, t1, t2);
      else if (isOpX<BSGT>(e))
        res = Z3_mk_bvsgt(ctx, t1, t2);
      else if (isOpX<BXOR>(e))
        res = Z3_mk_bvxor(ctx, t1, t2);
      else if (isOpX<BNAND>(e))
        res = Z3_mk_bvnand(ctx, t1, t2);
      else if (isOpX<BNOR>(e))
        res = Z3_mk_bvnor(ctx, t1, t2);
      else if (isOpX<BXNOR>(e))
        res = Z3_mk_bvxnor(ctx, t1, t2);
      else if (isOpX<BCONCAT>(e))
        res = Z3_mk_concat(ctx, t1, t2);
      else if (isOpX<BSHL>(e))
        res = Z3_mk_bvshl(ctx, t1, t2);
      else if (isOpX<BLSHR>(e))
        res = Z3_mk_bvlshr(ctx, t1, t2);
      else if (isOpX<BASHR>(e))
        res = Z3_mk_bvashr(ctx, t1, t2);

      else
        return M::marshal(e, ctx, cache, seen);
    } else if (isOpX<BEXTRACT>(e)) {
      assert(bv::high(e) >= bv::low(e));
      z3::ast a(ctx, marshal(bv::earg(e), ctx, cache, seen));
      res = Z3_mk_extract(ctx, bv::high(e), bv::low(e), a);
    } else if (isOpX<AND>(e) || isOpX<OR>(e) || isOpX<ITE>(e) ||
               isOpX<XOR>(e) || isOpX<PLUS>(e) || isOpX<MINUS>(e) ||
               isOpX<MULT>(e) || isOpX<STORE>(e) || isOpX<ARRAY_MAP>(e)) {
      std::vector<z3::ast> pinned;
      std::vector<Z3_ast> args;

      for (ENode::args_iterator it = e->args_begin(), end = e->args_end();
           it != end; ++it) {
        z3::ast a = z3::ast(ctx, marshal(*it, ctx, cache, seen));
        args.push_back(a);
        pinned.push_back(a);
      }

      if (isOp<ITE>(e)) {
        assert(e->arity() == 3);
        res = Z3_mk_ite(ctx, args[0], args[1], args[2]);
      } else if (isOp<AND>(e))
        res = Z3_mk_and(ctx, args.size(), &args[0]);
      else if (isOp<OR>(e))
        res = Z3_mk_or(ctx, args.size(), &args[0]);
      else if (isOp<PLUS>(e))
        res = Z3_mk_add(ctx, args.size(), &args[0]);
      else if (isOp<MINUS>(e))
        res = Z3_mk_sub(ctx, args.size(), &args[0]);
      else if (isOp<MULT>(e))
        res = Z3_mk_mul(ctx, args.size(), &args[0]);
      else if (isOp<STORE>(e)) {
        assert(e->arity() == 3);
        res = Z3_mk_store(ctx, args[0], args[1], args[2]);
      } else if (isOp<ARRAY_MAP>(e)) {
        Z3_func_decl fdecl = reinterpret_cast<Z3_func_decl>(args[0]);
        res = Z3_mk_map(ctx, fdecl, e->arity() - 1, &args[1]);
      }
    } else
      return M::marshal(e, ctx, cache, seen);

    if (res == nullptr)
      ctx.check_error();
    if (res == nullptr)
      errs() << "Failed to marshal: " << *e << "\n";

    assert(res != nullptr);
    z3::ast final(ctx, res);
    seen.insert(expr_ast_map::value_type(e, final));

    return final;
  }
};

template <typename U> struct BasicExprUnmarshal {
  template <typename C>
  static Expr unmarshal(const z3::ast &z, ExprFactory &efac, C &cache,
                        ast_expr_map &seen) {
    z3::context &ctx = z.ctx();

    Z3_lbool bVal = Z3_get_bool_value(ctx, z);
    if (bVal == Z3_L_TRUE)
      return mk<TRUE>(efac);
    if (bVal == Z3_L_FALSE)
      return mk<FALSE>(efac);

    Z3_ast_kind kind = z.kind();

    if (kind == Z3_NUMERAL_AST) {

      Z3_sort sort = Z3_get_sort(ctx, z);
      std::string snum = Z3_get_numeral_string(ctx, z);
      switch (Z3_get_sort_kind(ctx, sort)) {
      case Z3_REAL_SORT:
        return mkTerm(mpq_class(snum), efac);
      case Z3_INT_SORT:
        return mkTerm(mpz_class(snum), efac);
      case Z3_BV_SORT:
        return bv::bvnum(mpz_class(snum), Z3_get_bv_sort_size(ctx, sort), efac);
      default:
        assert(0 && "Unsupported numeric constant");
      }
    } else if (kind == Z3_SORT_AST) {
      Z3_sort sort = reinterpret_cast<Z3_sort>(static_cast<Z3_ast>(z));
      Expr domain, range;

      switch (Z3_get_sort_kind(ctx, sort)) {
      case Z3_BOOL_SORT:
        return sort::boolTy(efac);
      case Z3_INT_SORT:
        return sort::intTy(efac);
      case Z3_REAL_SORT:
        return sort::realTy(efac);
      case Z3_BV_SORT:
        return bv::bvsort(Z3_get_bv_sort_size(ctx, sort), efac);
      case Z3_ARRAY_SORT:
        domain = unmarshal(
            z3::ast(ctx,
                    Z3_sort_to_ast(ctx, Z3_get_array_sort_domain(ctx, sort))),
            efac, cache, seen);
        range = unmarshal(
            z3::ast(ctx,
                    Z3_sort_to_ast(ctx, Z3_get_array_sort_range(ctx, sort))),
            efac, cache, seen);
        return sort::arrayTy(domain, range);
      default:
        assert(0 && "Unsupported sort");
      }
    } else if (kind == Z3_VAR_AST) {
      unsigned idx = Z3_get_index_value(ctx, z);
      z3::ast zsort(ctx, Z3_sort_to_ast(ctx, Z3_get_sort(ctx, z)));
      Expr sort = unmarshal(zsort, efac, cache, seen);
      return bind::bvar(idx, sort);
    }

    else if (kind == Z3_FUNC_DECL_AST) {
      {
        typename C::const_iterator it = cache.find(z);
        if (it != cache.end())
          return it->second;
      }
      Z3_func_decl fdecl = Z3_to_func_decl(ctx, z);

      Z3_symbol symname = Z3_get_decl_name(ctx, fdecl);

      Expr name;
      switch (Z3_get_symbol_kind(ctx, symname)) {
      case Z3_STRING_SYMBOL:
        name = mkTerm<std::string>(Z3_get_symbol_string(ctx, symname), efac);
        break;
      case Z3_INT_SYMBOL:
        name = mkTerm<mpz_class>(Z3_get_symbol_int(ctx, symname), efac);
        break;
      }
      assert(name);

      ExprVector type;
      for (unsigned p = 0; p < Z3_get_domain_size(ctx, fdecl); ++p) {
        Z3_sort sort = Z3_get_domain(ctx, fdecl, p);
        type.push_back(unmarshal(z3::ast(ctx, Z3_sort_to_ast(ctx, sort)), efac,
                                 cache, seen));
      }

      type.push_back(
          unmarshal(z3::ast(ctx, Z3_sort_to_ast(ctx, Z3_get_range(ctx, fdecl))),
                    efac, cache, seen));

      return bind::fdecl(name, type);
    } else if (kind == Z3_QUANTIFIER_AST) {
      ExprVector args;
      unsigned num_bound = Z3_get_quantifier_num_bound(ctx, z);
      args.reserve(num_bound + 1);
      for (unsigned i = 0; i < num_bound; ++i) {
        Z3_func_decl decl =
            Z3_mk_func_decl(ctx, Z3_get_quantifier_bound_name(ctx, z, i), 0,
                            nullptr, Z3_get_quantifier_bound_sort(ctx, z, i));
        z3::ast zdecl(ctx, Z3_func_decl_to_ast(ctx, decl));
        args.push_back(unmarshal(zdecl, efac, cache, seen));
        assert(args.back().get());
      }
      args.push_back(unmarshal(z3::ast(ctx, Z3_get_quantifier_body(ctx, z)),
                               efac, cache, seen));
      if (Z3_is_quantifier_forall(ctx, z))
        return mknary<FORALL>(args);
      else if (Z3_is_quantifier_exists(ctx, z))
        return mknary<EXISTS>(args);

      assert(Z3_is_lambda(ctx, z));
      return mknary<LAMBDA>(args);
    }

    if (kind != Z3_APP_AST)
      errs() << boost::lexical_cast<std::string>(z) << "\n";

    assert(kind == Z3_APP_AST);
    Z3_app app = Z3_to_app(ctx, z);
    Z3_func_decl fdecl = Z3_get_app_decl(ctx, app);
    Z3_decl_kind dkind = Z3_get_decl_kind(ctx, fdecl);

    if (dkind == Z3_OP_NOT) {
      assert(Z3_get_app_num_args(ctx, app) == 1);
      return mk<NEG>(unmarshal(z3::ast(ctx, Z3_get_app_arg(ctx, app, 0)), efac,
                               cache, seen));
    }
    if (dkind == Z3_OP_UMINUS)
      return mk<UN_MINUS>(unmarshal(z3::ast(ctx, Z3_get_app_arg(ctx, app, 0)),
                                    efac, cache, seen));

    // XXX ignore to_real and to_int operators
    if (dkind == Z3_OP_TO_REAL || dkind == Z3_OP_TO_INT)
      return unmarshal(z3::ast(ctx, Z3_get_app_arg(ctx, app, 0)), efac, cache,
                       seen);

    if (dkind == Z3_OP_BNOT)
      return mk<BNOT>(unmarshal(z3::ast(ctx, Z3_get_app_arg(ctx, app, 0)), efac,
                                cache, seen));
    if (dkind == Z3_OP_BNEG)
      return mk<BNEG>(unmarshal(z3::ast(ctx, Z3_get_app_arg(ctx, app, 0)), efac,
                                cache, seen));
    if (dkind == Z3_OP_BREDAND)
      return mk<BREDAND>(unmarshal(z3::ast(ctx, Z3_get_app_arg(ctx, app, 0)),
                                   efac, cache, seen));
    if (dkind == Z3_OP_BREDOR)
      return mk<BREDOR>(unmarshal(z3::ast(ctx, Z3_get_app_arg(ctx, app, 0)),
                                  efac, cache, seen));
    if (dkind == Z3_OP_SIGN_EXT || dkind == Z3_OP_ZERO_EXT) {
      Expr sort =
          bv::bvsort(Z3_get_bv_sort_size(ctx, Z3_get_sort(ctx, z)), efac);
      Expr arg = unmarshal(z3::ast(ctx, Z3_get_app_arg(ctx, app, 0)), efac,
                           cache, seen);
      switch (dkind) {
      case Z3_OP_SIGN_EXT:
        return mk<BSEXT>(arg, sort);
      case Z3_OP_ZERO_EXT:
        return mk<BZEXT>(arg, sort);
      default:
        assert(0);
      }
    }

    if (dkind == Z3_OP_EXTRACT) {
      Expr arg = unmarshal(z3::ast(ctx, Z3_get_app_arg(ctx, app, 0)), efac,
                           cache, seen);

      Z3_func_decl d = Z3_get_app_decl(ctx, app);
      unsigned high = Z3_get_decl_int_parameter(ctx, d, 0);
      unsigned low = Z3_get_decl_int_parameter(ctx, d, 1);
      return bv::extract(high, low, arg);
    }

    if (dkind == Z3_OP_AS_ARRAY) {
      z3::ast zdecl(
          ctx, Z3_func_decl_to_ast(ctx, Z3_get_as_array_func_decl(ctx, z)));
      return mk<AS_ARRAY>(unmarshal(zdecl, efac, cache, seen));
    }

    {
      typename C::const_iterator it = cache.find(z);
      if (it != cache.end())
        return it->second;
    }
    {
      typename ast_expr_map::const_iterator it = seen.find(z);
      if (it != seen.end())
        return it->second;
    }

    Expr e;
    ExprVector args;
    for (size_t i = 0; i < (size_t)Z3_get_app_num_args(ctx, app); i++)
      args.push_back(unmarshal(z3::ast(ctx, Z3_get_app_arg(ctx, app, i)), efac,
                               cache, seen));

    /** newly introduced Z3 symbol */
    if (dkind == Z3_OP_UNINTERPRETED) {
      Expr res = bind::fapp(
          unmarshal(z3::func_decl(ctx, fdecl), efac, cache, seen), args);
      // -- XXX maybe use seen instead. not sure what is best.
      cache.insert(typename C::value_type(z, res));
      return res;
    }

    switch (dkind) {
    case Z3_OP_ITE:
      e = mknary<ITE>(args.begin(), args.end());
      break;
    case Z3_OP_AND:
      e = mknary<AND>(args.begin(), args.end());
      break;
    case Z3_OP_OR:
      e = mknary<OR>(args.begin(), args.end());
      break;
    case Z3_OP_XOR:
      e = mknary<XOR>(args.begin(), args.end());
      break;
    case Z3_OP_IFF:
      e = mknary<IFF>(args.begin(), args.end());
      break;
    case Z3_OP_IMPLIES:
      e = mknary<IMPL>(args.begin(), args.end());
      break;
    case Z3_OP_EQ:
      e = mknary<EQ>(args.begin(), args.end());
      break;
    case Z3_OP_LT:
      e = mknary<LT>(args.begin(), args.end());
      break;
    case Z3_OP_GT:
      e = mknary<GT>(args.begin(), args.end());
      break;
    case Z3_OP_LE:
      e = mknary<LEQ>(args.begin(), args.end());
      break;
    case Z3_OP_GE:
      e = mknary<GEQ>(args.begin(), args.end());
      break;
    case Z3_OP_ADD:
      e = mknary<PLUS>(args.begin(), args.end());
      break;
    case Z3_OP_SUB:
      e = mknary<MINUS>(args.begin(), args.end());
      break;
    case Z3_OP_MUL:
      e = mknary<MULT>(args.begin(), args.end());
      break;
    case Z3_OP_DIV:
      e = mknary<DIV>(args.begin(), args.end());
      break;
    case Z3_OP_IDIV:
      e = mknary<IDIV>(args.begin(), args.end());
      break;
    case Z3_OP_MOD:
      e = mknary<MOD>(args.begin(), args.end());
      break;
    case Z3_OP_REM:
      e = mknary<REM>(args.begin(), args.end());
      break;
    case Z3_OP_CONST_ARRAY: {
      assert(args.size() == 1);
      Z3_sort sort = Z3_get_sort(ctx, z);
      Expr domain = unmarshal(
          z3::ast(ctx,
                  Z3_sort_to_ast(ctx, Z3_get_array_sort_domain(ctx, sort))),
          efac, cache, seen);

      e = op::array::constArray(domain, args[0]);
    } break;
    case Z3_OP_STORE:
      e = mknary<STORE>(args.begin(), args.end());
      break;
    case Z3_OP_SELECT:
      e = mknary<SELECT>(args.begin(), args.end());
      break;
    case Z3_OP_BADD:
      e = mknary<BADD>(args.begin(), args.end());
      break;
    case Z3_OP_BSUB:
      e = mknary<BSUB>(args.begin(), args.end());
      break;
    case Z3_OP_BMUL:
      e = mknary<BMUL>(args.begin(), args.end());
      break;
    case Z3_OP_BSDIV:
      e = mknary<BSDIV>(args.begin(), args.end());
      break;
    case Z3_OP_BUDIV:
      e = mknary<BUDIV>(args.begin(), args.end());
      break;
    case Z3_OP_BSREM:
      e = mknary<BSREM>(args.begin(), args.end());
      break;
    case Z3_OP_BUREM:
      e = mknary<BUREM>(args.begin(), args.end());
      break;
    case Z3_OP_BSMOD:
      e = mknary<BSMOD>(args.begin(), args.end());
      break;
    case Z3_OP_ULEQ:
      e = mknary<BULE>(args.begin(), args.end());
      break;
    case Z3_OP_SLEQ:
      e = mknary<BSLE>(args.begin(), args.end());
      break;
    case Z3_OP_UGEQ:
      e = mknary<BUGE>(args.begin(), args.end());
      break;
    case Z3_OP_SGEQ:
      e = mknary<BSGE>(args.begin(), args.end());
      break;
    case Z3_OP_ULT:
      e = mknary<BULT>(args.begin(), args.end());
      break;
    case Z3_OP_SLT:
      e = mknary<BSLT>(args.begin(), args.end());
      break;
    case Z3_OP_UGT:
      e = mknary<BUGT>(args.begin(), args.end());
      break;
    case Z3_OP_SGT:
      e = mknary<BSGT>(args.begin(), args.end());
      break;
    case Z3_OP_BAND:
      e = mknary<BAND>(args.begin(), args.end());
      break;
    case Z3_OP_BOR:
      e = mknary<BOR>(args.begin(), args.end());
      break;
    case Z3_OP_BXOR:
      e = mknary<BXOR>(args.begin(), args.end());
      break;
    case Z3_OP_BNAND:
      e = mknary<BNAND>(args.begin(), args.end());
      break;
    case Z3_OP_BNOR:
      e = mknary<BNOR>(args.begin(), args.end());
      break;
    case Z3_OP_BXNOR:
      e = mknary<BXNOR>(args.begin(), args.end());
      break;
    case Z3_OP_BSHL:
      e = mknary<BSHL>(args.begin(), args.end());
      break;
    case Z3_OP_BLSHR:
      e = mknary<BLSHR>(args.begin(), args.end());
      break;
    case Z3_OP_BASHR:
      e = mknary<BASHR>(args.begin(), args.end());
      break;
    case Z3_OP_CONCAT:
      e = mknary<BCONCAT>(args.begin(), args.end());
      break;
    default:
      return U::unmarshal(z, efac, cache, seen);
    }

    seen[z] = e;
    return e;
  }
};

typedef ZContext<BasicExprMarshal<FailMarshal>,
                 BasicExprUnmarshal<FailUnmarshal>>
    EZ3;
} // namespace ufo

#endif
