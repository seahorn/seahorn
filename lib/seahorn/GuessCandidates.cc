#include "seahorn/GuessCandidates.hh"
#include "ufo/Expr.hpp"
#include "ufo/Smt/EZ3.hh"
#include <fstream>
#include <iostream>
#include <boost/tokenizer.hpp>

namespace seahorn
{
  ExprVector applyTemplatesFromExperimentFile(Expr fdecl, const std::string &filepath)
  {
    ExprVector bvars;
    ExprVector lemmas;

    int bvar_count = 0;
    for(int i=0; i<bind::domainSz(fdecl); i++)
    {
      if(isOpX<INT_TY>(bind::domainTy(fdecl, i)))
      {
        Expr bvar = bind::bvar(i, mk<INT_TY>(bind::domainTy(fdecl, i)->efac()));
        bvars.push_back(bvar);
        bvar_count ++;
      }
    }
    Expr one = mkTerm<mpz_class> (1, fdecl->efac());
    Expr zero = mkTerm<mpz_class> (0, fdecl->efac());
    Expr two = mkTerm<mpz_class> (2, fdecl->efac());
    if(bvar_count == 0)
    {
      lemmas.push_back(mk<TRUE>(fdecl->efac()));
    }
    else if(bvar_count == 1)
    {
      lemmas.push_back(mk<GEQ>(bvars[0], one));
      lemmas.push_back(mk<LEQ>(bvars[0], one));
      lemmas.push_back(mk<GEQ>(bvars[0], zero));
      lemmas.push_back(mk<GEQ>(bvars[0], two));
      lemmas.push_back(mk<LEQ>(bvars[0], two));
      parseLemmasFromExpFile(bvars[0], lemmas, filepath);
    }
    else
    {
      for(int i=0; i<bvars.size(); i++)
      {
        lemmas.push_back(mk<GEQ>(bvars[i], one));
        lemmas.push_back(mk<LEQ>(bvars[i], one));
        lemmas.push_back(mk<GEQ>(bvars[i], zero));
        lemmas.push_back(mk<GEQ>(bvars[i], two));
        lemmas.push_back(mk<LEQ>(bvars[i], two));
        parseLemmasFromExpFile(bvars[i], lemmas, filepath);
      }
    }
    return lemmas;
  }

  void parseLemmasFromExpFile(Expr bvar, ExprVector& lemmas, const std::string &filepath)
  {
    std::ifstream in(filepath);
    std::string line;
    if(in)
    {
      while (getline (in, line))
      {
        boost::char_separator<char> sep(",");
        typedef boost::tokenizer< boost::char_separator<char>> t_tokenizer;
        t_tokenizer tok(line, sep);
        std::string op = *(tok.begin());
        std::string number = *(++tok.begin());
        int value = std::atoi(number.c_str());
        if(op == "LEQ") lemmas.push_back(mk<LEQ>(bvar, mkTerm<mpz_class>(value, bvar->efac())));
        else if(op == "GEQ") lemmas.push_back(mk<GEQ>(bvar, mkTerm<mpz_class>(value, bvar->efac())));
        else if(op == "LT") lemmas.push_back(mk<LT>(bvar, mkTerm<mpz_class>(value, bvar->efac())));
        else if(op == "GT") lemmas.push_back(mk<GT>(bvar, mkTerm<mpz_class>(value, bvar->efac())));
      }
    }
    else
    {
      //errs() << "FILE NOT EXIST!\n";
      return;
    }
  }

  //	ExprVector relToCand(Expr fdecl)
  //	{
  //		ExprVector bvars;
  //		ExprVector bins;   // a vector of LT expressions
  //		Expr cand = NULL;
  //
  //		int bvar_count = 0;
  //		unsigned i = 0;
  //		for (i=0; i < bind::domainSz(fdecl); i++)
  //		{
  //			// if its type is INT
  //			if (isOpX<INT_TY>(bind::domainTy(fdecl, i)))
  //			{
  //				// what is efac?
  //				Expr bvar = bind::bvar (i, mk<INT_TY>(bind::domainTy(fdecl, i)->efac())); //the id of bvar is the same as related arg index
  //				bvars.push_back(bvar);
  //				bvar_count ++;
  //			}
  //		}
  //
  //		//What if there's no bvar?
  //		if(bvar_count == 0)
  //		{
  //			//cand = mk<TRUE>(fdecl->efac());
  //			bins.push_back(mk<TRUE>(fdecl->efac()));
  //		}
  //		// if there is only one bvar, create a int constant and make an lt expr
  //		else if(bvar_count == 1)
  //		{
  //			Expr zero = mkTerm<mpz_class> (0, fdecl->efac());
  //			//cand = mk<LT>(bvars[0], zero);
  //			bins.push_back(mk<LT>(bvars[0], zero));
  //		}
  //		// if there are more than two bvars, make an lt expr
  //		else if(bvar_count == 2)
  //		{
  //			Expr lt1 = mk<LT>(bvars[0], bvars[1]);
  //			Expr lt2 = mk<LT>(bvars[1], bvars[0]);
  //			bins.push_back(lt1);
  //			bins.push_back(lt2);
  //
  //			//cand = mknary<AND>(bins.begin(), bins.end());
  //		}
  //		else // bvar_count > 2
  //		{
  //			for(int j=0; j<bvars.size()-1; j++)
  //			{
  //				Expr lt = mk<LT>(bvars[j], bvars[j+1]);
  //				bins.push_back(lt);
  //			}
  //			//cand = mknary<AND>(bins.begin(), bins.end());
  //		}
  //		return bins;
  //	}

  ExprVector relToCand(Expr fdecl)
  {
    ExprVector bvars;
    ExprVector bins;   // a vector of LT expressions
    Expr cand = NULL;

    int bvar_count = 0;
    unsigned i = 0;
    for (i=0; i < bind::domainSz(fdecl); i++)
    {
      // if its type is INT
      if (isOpX<INT_TY>(bind::domainTy(fdecl, i)))
      {
        // what is efac?
        Expr bvar = bind::bvar (i, mk<INT_TY>(bind::domainTy(fdecl, i)->efac())); //the id of bvar is the same as related arg index
        bvars.push_back(bvar);
        bvar_count ++;
      }
    }

    //What if there's no bvar?
    if(bvar_count == 0)
    {
      //cand = mk<TRUE>(fdecl->efac());
      bins.push_back(mk<TRUE>(fdecl->efac()));
    }
    // if there is only one bvar, create a int constant and make an lt expr
    else if(bvar_count == 1)
    {
      Expr zero = mkTerm<mpz_class> (0, fdecl->efac());
      //cand = mk<LT>(bvars[0], zero);
      bins.push_back(mk<LT>(bvars[0], zero));
    }
    // if there are more than two bvars, make an lt expr
    else if(bvar_count == 2)
    {
      Expr lt1 = mk<LT>(bvars[0], bvars[1]);
      Expr lt2 = mk<LT>(bvars[1], bvars[0]);
      bins.push_back(lt1);
      bins.push_back(lt2);

      //cand = mknary<AND>(bins.begin(), bins.end());
      //cand = mk<LT>(bvars[0], bvars[1]);
    }
    else // bvar_count > 2
    {
      for(int j=0; j<bvars.size()-1; j++)
      {
        Expr lt = mk<LT>(bvars[j], bvars[j+1]);
        bins.push_back(lt);
      }
      //cand = mknary<AND>(bins.begin(), bins.end());
    }

    return bins;
  }

}
