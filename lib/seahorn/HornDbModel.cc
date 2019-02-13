#include "seahorn/HornDbModel.hh"
#include "seahorn/HornifyModule.hh"
#include "seahorn/HornClauseDB.hh"

#include "ufo/Expr.hpp"
#include <vector>

#include "seahorn/Support/Stats.hh"

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
}
