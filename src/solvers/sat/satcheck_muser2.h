/*******************************************************************\

Module: Interface to MUSER2

Author: Peter Schrammel

\*******************************************************************/

#ifndef CPROVER_SATCHECK_MUSER2_H
#define CPROVER_SATCHECK_MUSER2_H

#ifdef HAVE_MUSER2

#include "cnf.h"

//solver names
#define MUSER2_GLUCOSE "glucoses"
#define MUSER2_MINISAT2 "minisats"
#define MUSER2_PICOSAT "picosat"
#define MUSER2_LINGELING "lingeling"

//heuristics
#define MUSER2_MAXMIN 0
#define MUSER2_MINMAX 3
#define MUSER2_RANDOM 4

class muser2;

class satcheck_muser2t:public cnf_solvert
{
public:
  explicit satcheck_muser2t(const char* solver_name);
  virtual ~satcheck_muser2t();

  //MUSer2 configuration
  void set_order(int _order) { order = _order; }
  void set_cpu_time_limit(double _cpu_time_limit) 
    { cpu_time_limit = _cpu_time_limit; }
  void set_iter_limit(int _iter_limit) { iter_limit = _iter_limit; }
  
  virtual const std::string solver_text();
  virtual resultt prop_solve();
  virtual tvt l_get(literalt a) const;

  virtual void lcnf(const bvt &bv);
  virtual void set_assignment(literalt a, bool value);

  virtual void set_assumptions(const bvt &_assumptions);
  
  virtual bool is_in_conflict(literalt a) const;
  virtual bool has_set_assumptions() const { return true; }
  virtual bool has_is_in_conflict() const { return true; }
  
protected:
  muser2 *solver;
  int order;
  double cpu_time_limit;
  unsigned iter_limit;
  std::vector<unsigned> mus;
  bvt assumptions;

  void add_clause(const bvt &bv, bool is_assumption);
};

#endif

#endif
