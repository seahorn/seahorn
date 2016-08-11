#ifndef PREDICATE_ABSTRACTION__HH_
#define PREDICATE_ABSTRACTION__HH_

#include "llvm/Pass.h"
#include "llvm/IR/Module.h"
#include "seahorn/HornClauseDB.hh"
#include "seahorn/HornifyModule.hh"

#include "ufo/Expr.hpp"
#include "ufo/Smt/Z3n.hpp"
#include "ufo/Smt/EZ3.hh"
#include "seahorn/HornClauseDBWto.hh"

namespace seahorn
{
	using namespace llvm;

	class HornDbModel
	{
	private:
		ExprMap relToDefMap;
	public:
		HornDbModel() {}
		void initAbstractDbModel(HornClauseDB &db, ZFixedPoint<EZ3> &fp);
		void addDef(Expr rel, Expr def);
		Expr& getDef(Expr rel) {return relToDefMap.find(rel)->second;}
		HornDbModel(ExprMap model) : relToDefMap(model) {}
		virtual ~HornDbModel(){}
		ExprMap& getRelToSolutionMap() {return relToDefMap;}
		void setRelToSolutionMap(ExprMap map) {relToDefMap = map;}
	};

	class HornModelConverter
	{
	public:
		// converts a model from one database to another. returns false on failure.
		virtual bool convert (HornDbModel &in, HornDbModel &out, std::map<Expr, Expr> &newToOldPredMap, HornClauseDB &abs_db) = 0;
	};

	class PredAbsHornModelConverter : public HornModelConverter
	{
	private:
		std::map<Expr, ExprMap> relToBvToTermMap;
	public:
		bool convert (HornDbModel &in, HornDbModel &out, std::map<Expr, Expr> &newToOldPredMap, HornClauseDB &abs_db);
		std::map<Expr, ExprMap>& getRelToBvToTermMap() {return relToBvToTermMap;}
	};

	class PredicateAbstraction : public llvm::ModulePass
	{
		std::unique_ptr<ufo::ZFixedPoint <ufo::EZ3> >  m_fp;
	public:
	    static char ID;

	    PredicateAbstraction() : ModulePass(ID) {}
	    virtual ~PredicateAbstraction() {}
	    virtual bool runOnModule (Module &M);
	    virtual void getAnalysisUsage (AnalysisUsage &AU) const;
	    virtual const char* getPassName () const {return "PredicateAbstraction";}

	private:
	    static std::map<Expr, Expr> oldToNewPredMap;
	    static std::map<Expr, Expr> newToOldPredMap;
	    static std::map<Expr, ExprVector> currentCandidates;

	public:
	    void guessCandidate(HornClauseDB &db);
	    ExprVector relToCand(Expr fdecl);
	    HornClauseDB runOnDB(HornClauseDB &db, PredAbsHornModelConverter &converter);
	    Expr fAppToCandApp(Expr fapp);
	    Expr applyArgsToBvars(Expr cand, Expr fapp);
	    ExprMap getBvarsToArgsMap(Expr fapp);
	    Expr extractTransitionRelation(HornRule r, HornClauseDB &db);

	    template<typename OutputIterator>
	    void get_all_pred_apps (Expr e, HornClauseDB &db, OutputIterator out);

	    template<typename OutputIterator>
	    void get_all_bvars (Expr e, OutputIterator out);

	    bool hasBvarInRule(HornRule r, HornClauseDB &db);

	    ufo::ZFixedPoint<ufo::EZ3>& getZFixedPoint () {return *m_fp;}
		void releaseMemory ()
		{
			m_fp.reset (nullptr);
//			for(std::map<Expr, Expr>::iterator it = predToBiMap.begin(); it!= predToBiMap.end(); ++it)
//			{
//				intrusive_ptr_release(it->second);
//			}
//			predToBiMap.clear();
//			for(std::map<Expr, Expr>::iterator it = predToBiPrimeMap.begin(); it!= predToBiPrimeMap.end(); ++it)
//			{
//				intrusive_ptr_release(it->second.get());
//			}
//			predToBiPrimeMap.clear();
//			for(std::map<Expr, Expr>::iterator it = oldToNewPredMap.begin(); it!=oldToNewPredMap.end(); ++it)
//			{
//				intrusive_ptr_release(it->second.get());
//			}
//			oldToNewPredMap.clear();
//			for(std::map<Expr, Expr>::iterator it = currentCandidates.begin(); it!= currentCandidates.end(); ++it)
//			{
//				intrusive_ptr_release(it->second.get());
//			}
//			currentCandidates.clear();
		}

		void printInvars (Function &F);
		void printInvars (Module &M);
	};
}

#endif
