/*******************************************************************\

Module: Z3 C++ API Backend

Author: Johanan Wahlang, wadkhlemshem@gmail.com
        Manasij Mukherjee, manasij7479@gmail.com

\*******************************************************************/

#ifndef CPROVER_SOLVERS_SMT2_Z3_CONV_H
#define CPROVER_SOLVERS_SMT2_Z3_CONV_H

#include <fstream>
#include <set>

#include <util/hash_cont.h>
#include <util/arith_tools.h>
#include <util/expr_util.h>
#include <util/std_types.h>
#include <util/std_expr.h>
#include <util/byte_operators.h>
#include <ansi-c/string_constant.h>

#include <langapi/language_util.h>

#include <solvers/prop/prop_conv.h>
#include <solvers/flattening/boolbv_width.h>
#include <solvers/flattening/pointer_logic.h>
#include <z3++.h>

class typecast_exprt;
class constant_exprt;
class index_exprt;
class member_exprt;

class z3_convt:public prop_convt
{
public:
  z3_convt(
    const namespacet &_ns,
    const std::string &_benchmark,
    const std::string &_notes,
    const std::string &_logic):
    prop_convt(_ns),
    use_FPA_theory(false),
    ns(_ns),
    benchmark(_benchmark),
    notes(_notes),
    logic(_logic),
    boolbv_width(_ns),
    params(context),
    solver(context),
    store(context),
    no_boolean_variables(0)
  {
    params.set("mbqi", true);
    solver.set(params);
  }

  virtual ~z3_convt() {}
  resultt dec_solve()
  {
    switch(solver.check())
    {
      case z3::unsat:   return D_UNSATISFIABLE;
      case z3::sat:     return D_SATISFIABLE;
      default:          return D_ERROR;
    }
  }

  bool use_FPA_theory;

  // overloading interfaces
  virtual literalt convert(const exprt &expr);

  virtual void set_frozen(literalt a) { /* not needed */ }
  virtual void set_to(const exprt &expr, bool value) override
  {
    if (value)
      solver.add(convert_expr(expr));
    else
      solver.add(!convert_expr(expr));
  }

  exprt get(const exprt &expr) const;
  std::string decision_procedure_text() const { return "Z3"; }
  virtual void print_assignment(std::ostream &out) const {}
  virtual tvt l_get(literalt l) const;
  virtual void set_assumptions(const bvt &bv) { assumptions=bv; throw 3;}

  virtual void new_context()
  {
    solver.push();
  }
 
  virtual void pop_context()
  {
    solver.pop(1);
  }

  z3::expr convert_expr(const exprt &) const ;
  z3::expr convert_literal(const literalt) const;

protected:
  const namespacet &ns;
  std::string benchmark, notes, logic;

  bvt assumptions;
  boolbv_widtht boolbv_width;

  mutable z3::context context;
  z3::params params;
  z3::solver solver;

  typedef hash_map_cont<irep_idt, int, irep_id_hash>
    identifier_mapt;

  mutable identifier_mapt identifier_map;
  mutable z3::expr_vector store;

  bool exists(const irep_idt &id) const
  {
    return identifier_map.find(id) != identifier_map.end();
  }
  z3::expr fetch(const irep_idt &id) const
  {
    return store[identifier_map[id]];
  }
  
  unsigned no_boolean_variables;
  std::vector<bool> boolean_assignment;

  z3::sort convert_type(const typet &type) const;

  // specific expressions go here
  z3::expr convert_constant(const constant_exprt &expr) const;
  z3::expr convert_identifier(const irep_idt &id, const typet &type) const;
};

#endif // CPROVER_SOLVERS_SMT2_Z3_CONV_H
