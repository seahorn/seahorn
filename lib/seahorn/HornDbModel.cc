#include "seahorn/HornDbModel.hh"
#include "seahorn/HornifyModule.hh"
#include "seahorn/HornClauseDB.hh"

#include "ufo/Expr.hpp"
#include "ufo/Smt/Z3n.hpp"
#include <vector>

#include "ufo/Stats.hh"

namespace seahorn
{
  void HornDbModel::addDef(Expr fapp, Expr lemma)
  {
	Expr lemma_def;

    if (isOpX<TRUE> (lemma) || isOpX<FALSE> (lemma))
    {
    	lemma_def = lemma;
    }
    else
    {
		assert (bind::isFapp (fapp));
		Expr fdecl = bind::fname(fapp);
		ExprMap actual_arg_to_bvar_map;
		for(int i=0; i<bind::domainSz(fdecl); i++)
		{
		  Expr arg_i = fapp->arg(i+1);
		  Expr arg_i_type = bind::domainTy(fdecl, i);
		  Expr bvar_i = bind::bvar(i, arg_i_type);
		  actual_arg_to_bvar_map.insert(std::make_pair(arg_i, bvar_i));
		}
		lemma_def = replace(lemma, actual_arg_to_bvar_map);
    }

    m_defs[bind::fname(fapp)] = lemma_def;
  }

  Expr HornDbModel::getDef(Expr fapp)
  {
    Expr fdecl = bind::fname(fapp);
    ExprMap::iterator it = m_defs.find(fdecl);

    if(it == m_defs.end())
      return mk<TRUE>(fdecl->efac());

    Expr lemma_def = it->second;

    ExprMap bvar_to_actual_arg_map;

    for(int i=0; i<bind::domainSz(fdecl); i++)
    {
      Expr arg_i = fapp->arg(i+1);
      Expr arg_i_type = bind::domainTy(fdecl, i);
      Expr bvar_i = bind::bvar(i, arg_i_type);
      bvar_to_actual_arg_map.insert(std::make_pair(bvar_i, arg_i));
    }

    Expr lemma = replace(lemma_def, bvar_to_actual_arg_map);
    return lemma;
  }

  bool HornDbModel::hasDef (Expr v)
  {
    if (bind::isFapp (v)) v = bind::fname (v);
    return m_defs.count (v);
  }

  void initDBModelFromFP(HornDbModel &dbModel, HornClauseDB &db, ZFixedPoint<EZ3> &fp)
  {
    for(Expr rel : db.getRelations ())
    {
      ExprVector actual_args;
      for(int i=0; i<bind::domainSz(rel); i++)
      {
        Expr V = mkTerm<std::string> ("V", rel->efac ());
        Expr arg_i_type = bind::domainTy(rel, i);
        // XXX use bvars instead of constants
        Expr var = bind::fapp(bind::constDecl(variant::variant(i, V), arg_i_type));
        actual_args.push_back (var);
      }
      Expr fapp = bind::fapp(rel, actual_args);
      Expr def_app = fp.getCoverDelta(fapp);
      dbModel.addDef(fapp, def_app);
    }
  }

  void initDBModelFromFile(HornDbModel &dbModel, HornClauseDB &db, EZ3& z3, const char *fname)
  {
	  Expr assert_conjunction = z3_from_smtlib_file(z3, fname);
	  outs() << "ASSERTION CONJUNCTIONS: " << *assert_conjunction << "\n";
	  ExprMap fappTocandAppMap;
	  ExprVector fapps;
	  for(int i=0; i<assert_conjunction->arity(); i++)
	  {
		  Expr impl = assert_conjunction->arg(i);
		  Expr fapp = impl->arg(0);
		  Expr cand_app = impl->arg(1);
		  fappTocandAppMap.insert(std::make_pair(fapp, cand_app));
		  fapps.push_back(fapp);
		  LOG("validate-inv", outs() << "FAPP:" << *fapp << "\n";);
		  LOG("validate-inv", outs() << "CANDAPP:" << *cand_app << "\n";);
	  }

	  for(Expr rel : db.getRelations())
	  {
		  outs() << "CURRENT REL: " << *rel << "\n";
		  for(ExprVector::iterator it = fapps.begin(); it != fapps.end(); ++it)
		  {
			  Expr fapp = *it;
			  std::ostringstream oss;
			  oss << bind::fname(rel);
			  std::ostringstream oss2;
			  oss2 << bind::fname(bind::fname(fapp));

			  if(oss.str() == oss2.str())
			  {
				  ExprVector args;

				  for(int i=0; i<bind::domainSz(bind::fname(fapp)); i++)
				  {
					  args.push_back(fapp->arg(i+1));
				  }

				  Expr rel_app = bind::fapp(rel, args);
				  Expr cand_app = fappTocandAppMap.find(fapp)->second;
				  outs() << "REL APP: " << *rel_app << "\n";
				  outs() << "CAND APP: " << *cand_app << "\n";
				  dbModel.addDef(rel_app, cand_app);
			  }
		  }
	  }
  }
}
