/*******************************************************************\

Module: Lockset Analysis

Author: Bjoern Wachter, bjoern.wachter@gmail.com

\*******************************************************************/

#ifndef CPROVER_POINTER_ANALYSIS_LOCK_SET_H
#define CPROVER_POINTER_ANALYSIS_LOCK_SET_H

#include <analyses/static_analysis.h>

#include <pointer-analysis/value_set_domain.h>
#include <pointer-analysis/value_sets.h>
#include <pointer-analysis/value_set_analysis.h>

typedef value_sett::object_mapt object_mapt;

class lock_set_domaint : public domain_baset
{
public:
  object_mapt object_map;


  value_set_analysist *value_set_analysis;

  inline bool merge(const lock_set_domaint &other, locationt to)
  {
    return value_sett::make_union(object_map, other.object_map);
  }

  bool merge_shared(
    const namespacet &ns,
    const lock_set_domaint &other,
    locationt to)
  {
    return value_sett::make_union(object_map, other.object_map);
  }

  virtual void initialize(
    const namespacet &ns,
    locationt l)
  {
  }

  virtual void transform(
    const namespacet &ns,
    locationt from_l,
    locationt to_l);

  // interface value_sets
  virtual void get_values(
    locationt l,
    const exprt &expr,
    value_setst::valuest &dest,
    const namespacet &ns)
  {
    (*value_set_analysis)[l].value_set.get_value_set(expr, dest, ns);
  }

  virtual void output(
    const namespacet &ns,
    std::ostream &out) const
  {
    value_sett::output(ns, out, object_map);
  }

  // interface value_sets
  virtual const value_sett& get_value_set(
    locationt l)
  {
    return (*value_set_analysis)[l].value_set;
  }

  //TODO: this should go away in future
  static void clean_update(const object_mapt &new_objects, 
			   object_mapt &lock_objects);

};


class xmlt;

class lock_set_analysist:
  public static_analysist<lock_set_domaint>
{
public:
  lock_set_analysist(const namespacet &_ns,
                     value_set_analysist &_value_set_analysis):
    static_analysist<lock_set_domaint>(_ns),
    value_set_analysis(_value_set_analysis)
   {
   }

  typedef static_analysist<lock_set_domaint> baset;

  // overloading
  virtual void initialize(const goto_programt &goto_program);
  virtual void initialize(const goto_functionst &goto_functions);

  friend void convert(
    const goto_functionst &goto_functions,
    const lock_set_analysist &lock_set_analysis,
    xmlt &dest);

  friend void convert(
    const goto_programt &goto_program,
    const lock_set_analysist &lock_set_analysis,
    xmlt &dest);

  void convert(
    const goto_programt &goto_program,
    const irep_idt &identifier,
    xmlt &dest) const;

  static std::string lock_function;
  static std::string unlock_function;

public:

  virtual void generate_state(locationt l);

  value_set_analysist &value_set_analysis;
};

#include <util/ui_message.h>

class goto_functionst;
class goto_programt;
class lock_set_analysist;

void show_lock_sets(
  ui_message_handlert::uit ui,
  const goto_functionst &goto_functions,
  const lock_set_analysist &lock_set_analysis);

void show_lock_sets(
  ui_message_handlert::uit ui,
  const goto_programt &goto_program,
  const lock_set_analysist &lock_set_analysis);

#endif
