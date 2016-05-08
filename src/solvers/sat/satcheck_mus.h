/*******************************************************************\

Module: Simple MUS extractor

Author: Peter Schrammel

\*******************************************************************/

#ifndef CPROVER_SATCHECK_MUS_H
#define CPROVER_SATCHECK_MUS_H

#include "cnf.h"

class satcheck_must:public cnf_solvert
{
public:
  explicit satcheck_must(cnf_solvert &_solver)
    : solver(_solver) {}
  virtual ~satcheck_must() {}

  //we override these 
  virtual const std::string solver_text();
  virtual resultt prop_solve();
  virtual void set_assumptions(const bvt &_assumptions);
  virtual bool is_in_conflict(literalt a) const;
  virtual bool has_set_assumptions() const { return true; }
  virtual bool has_is_in_conflict() const { return true; }

  //feed through to underlying solver
  virtual tvt l_get(literalt a) const { return solver.l_get(a); }
  virtual void lcnf(const bvt &bv) { solver.lcnf(bv); }
  virtual void set_assignment(literalt a, bool value)
    { solver.set_assignment(a, value); }
  virtual literalt land(literalt a, literalt b)
    { return solver.land(a,b); }
  virtual literalt lor(literalt a, literalt b)
    { return solver.lor(a,b); }
  virtual literalt land(const bvt &bv)
    { return solver.land(bv); }
  virtual literalt lor(const bvt &bv)
    { return solver.lor(bv); }
  virtual literalt lxor(const bvt &bv)
    { return solver.lxor(bv); }
  virtual literalt lnot(literalt a)
    { return solver.lnot(a); }
  virtual literalt lxor(literalt a, literalt b)
    { return solver.lxor(a,b); }
  virtual literalt lnand(literalt a, literalt b)
    { return solver.lnand(a,b); }
  virtual literalt lnor(literalt a, literalt b)
    { return solver.lnor(a,b); }
  virtual literalt lequal(literalt a, literalt b)
    { return solver.lequal(a,b); }
  virtual literalt limplies(literalt a, literalt b)
    { return solver.limplies(a,b); }
  virtual literalt lselect(literalt a, literalt b, literalt c)
    { return solver.lselect(a,b,c); } 
  virtual literalt new_variable() { return solver.new_variable(); }
  virtual size_t no_variables() const { return solver.no_variables(); }
  virtual void set_no_variables(size_t no) { solver.set_no_variables(no); }
  virtual size_t no_clauses() const { return solver.no_clauses(); }

protected:
  cnf_solvert &solver;
  bvt mus;
  bvt assumptions;
};

#endif
