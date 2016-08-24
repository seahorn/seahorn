#include "seahorn/HornDbModel.hh"
#include "seahorn/HornifyModule.hh"
#include "seahorn/HornClauseDB.hh"

#include "ufo/Expr.hpp"
#include <vector>

#include "ufo/Stats.hh"

namespace seahorn
{
	void HornDbModel::addDef(Expr fapp, Expr lemma)
	{
		if (isOpX<TRUE> (lemma) || isOpX<FALSE> (lemma))
		{
			relToDefMap.insert(std::pair<Expr, Expr>(bind::fname(fapp), lemma));
			return;
		}

		assert (bind::isFapp (fapp));

		Expr fdecl = bind::fname(fapp);

		ExprMap actual_arg_to_bvar_map;

		for(int i=0; i<bind::domainSz(fdecl); i++)
		{
			Expr arg_i = fapp->arg(i+1);
			Expr arg_i_type = bind::domainTy(fdecl, i);
			Expr bvar_i = bind::bvar(i, arg_i_type);
			actual_arg_to_bvar_map.insert(std::pair<Expr, Expr>(arg_i, bvar_i));
		}

		Expr lemma_def = replace(lemma, actual_arg_to_bvar_map);

		relToDefMap.insert(std::pair<Expr, Expr>(bind::fname(fapp), lemma_def));
	}

	Expr HornDbModel::getDef(Expr fapp)
	{
		Expr fdecl = bind::fname(fapp);
		ExprMap::iterator it = relToDefMap.find(fdecl);

		if(it == relToDefMap.end())
	    {
			return mk<TRUE>(fdecl->efac());
	    }

	    Expr lemma_def = it->second;

		ExprMap bvar_to_actual_arg_map;

		for(int i=0; i<bind::domainSz(fdecl); i++)
		{
			Expr arg_i = fapp->arg(i+1);
			Expr arg_i_type = bind::domainTy(fdecl, i);
			Expr bvar_i = bind::bvar(i, arg_i_type);
			bvar_to_actual_arg_map.insert(std::pair<Expr, Expr>(bvar_i, arg_i));
		}

		Expr lemma = replace(lemma_def, bvar_to_actual_arg_map);
		return lemma;
	}

	void initDBModelFromFP(HornDbModel &dbModel, HornClauseDB &db, ZFixedPoint<EZ3> &fp)
	{
		for(Expr rel : db.getRelations())
		{
			ExprVector actual_args;
			for(int i=0; i<bind::domainSz(rel); i++)
			{
				Expr arg_i_type = bind::domainTy(rel, i);
				Expr var = bind::fapp(bind::constDecl(variant::variant(i, mkTerm<std::string> ("V", rel->efac ())), arg_i_type));
				actual_args.push_back(var);
			}
			Expr fapp = bind::fapp(rel, actual_args);
			Expr def_app = fp.getCoverDelta(fapp);
			dbModel.addDef(fapp, def_app);
		}
	}
}
