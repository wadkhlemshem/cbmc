/*******************************************************************\

Module: Simple MUS extractor

Author: Peter Schrammel

\*******************************************************************/

#include <cassert>
#include <stack>

#include <util/threeval.h>

#include "satcheck_mus.h"

/*******************************************************************\

Function: satcheck_must::solver_text

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

const std::string satcheck_must::solver_text()
{
  return solver.solver_text()+" with MUS extraction";
}


/*******************************************************************\

Function: satcheck_must::prop_solve

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

propt::resultt satcheck_must::prop_solve()
{
  propt::resultt result = solver.prop_solve();
  if(result!=P_UNSATISFIABLE) 
    return result;

  //extract MUS using 1-deletion heuristic

  //get initial MUS
  for(int j=0; j<assumptions.size(); j++)
  {
    const literalt &a = assumptions[j];
    if(solver.is_in_conflict(a))
    {
      mus.push_back(a);
      solver.set_frozen(a);
    }
  }

  for(int i=0; i<mus.size(); i++)
  {
    literalt l = mus.front();
    mus.erase(mus.begin());

    solver.set_assumptions(mus);
    if(solver.prop_solve()==P_UNSATISFIABLE)
    {
      mus.clear();
      for(int j=0; j<assumptions.size(); j++)
      {
	const literalt &a = assumptions[j];
	if(solver.is_in_conflict(a))
	  mus.push_back(a);
      }
    }
    else mus.push_back(l);
  }

  return P_UNSATISFIABLE;
}

/*******************************************************************\

Function: satcheck_must::is_in_conflict

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

bool satcheck_must::is_in_conflict(literalt a) const
{
  for(int i=0; i<mus.size(); i++)
    if(mus[i]==a)
      return true;

  return false;
}

/*******************************************************************\

Function: satcheck_must::set_assumptions

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void satcheck_must::set_assumptions(const bvt &bv)
{
  assumptions=bv;
  solver.set_assumptions(bv);
}

