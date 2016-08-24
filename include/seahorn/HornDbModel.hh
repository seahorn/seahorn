#ifndef HORNDBMODEL__HH_
#define HORNDBMODEL__HH_

#include "seahorn/HornClauseDB.hh"
#include "seahorn/HornifyModule.hh"

#include "ufo/Expr.hpp"
#include "ufo/Smt/Z3n.hpp"
#include "ufo/Smt/EZ3.hh"

namespace seahorn
{
	class HornDbModel
	{
	private:
		ExprMap relToDefMap;
	public:
		HornDbModel() {}
		void addDef(Expr fapp, Expr lemma);
		Expr getDef(Expr fapp);
		virtual ~HornDbModel() {}
	};

	void initDBModelFromFP(HornDbModel &dbModel, HornClauseDB &db, ZFixedPoint<EZ3> &fp);
}

#endif
