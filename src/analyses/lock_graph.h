/*******************************************************************\

Module: Lock graph Analysis

Author: Peter Schrammel

\*******************************************************************/

#ifndef CPROVER_POINTER_ANALYSIS_LOCK_GRAPH_H
#define CPROVER_POINTER_ANALYSIS_LOCK_GRAPH_H

#include "lock_set_analysis.h"
#include "which_threads.h"

#include <util/graph.h>

typedef value_sett::object_mapt object_mapt;

class lock_graph_domaint : public domain_baset
{
public:

  class edget {
  public:
    std::set<irep_idt> thread_categories; 
    edget() {}
    edget(irep_idt _thread_category)
    {
      thread_categories.insert(_thread_category);
    }
  };
  
  typedef value_sett::object_map_dt lock_typet;
  class nodet : public graph_nodet<edget> {
  public:
    bool is_thread; // thread or lock node
    irep_idt thread_category; 
    lock_typet lock;

    nodet() {}
    nodet(irep_idt _thread_category):
      is_thread(true), thread_category(_thread_category)
    {}
    nodet(const lock_typet &_lock):
      is_thread(false), lock(_lock)
    {}
  };

  typedef graph<nodet> grapht;
  typedef std::map<irep_idt,std::list<unsigned> > current_lockst;

  current_lockst *current_locks;
  grapht *lock_graph;

  static bool has_node(const grapht &_graph, const nodet &node, grapht::node_indext &n);
  void push_lock(const namespacet &ns,
		 irep_idt thread_category,
		 const lock_typet &lock);
  void pop_lock(const namespacet &ns,
		irep_idt thread_category,
		const lock_typet &lock); 

  static void output_lock(const namespacet &ns, std::ostream &out, 
			  const lock_typet &lock);
  static void output_thread_categories(std::ostream &out,
			       const std::set<irep_idt> &thread_categories);

  lock_set_analysist *lock_set_analysis;
  which_threads_internalt *which_threads;

  inline bool merge(const lock_graph_domaint &other, locationt to) 
    { return false; }

  bool merge_shared(
    const namespacet &ns,
    const lock_graph_domaint &other,
    locationt to)
  {
    return merge(other, to);
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

};


class xmlt;

class lock_grapht:
  public static_analysist<lock_graph_domaint>
{
public:
  lock_grapht(const namespacet &_ns,
	      lock_set_analysist &_lock_set_analysis,
              which_threads_internalt &_which_threads):
    static_analysist<lock_graph_domaint>(_ns),
    lock_set_analysis(_lock_set_analysis),
    which_threads(_which_threads)
   {
     for(which_threads_internalt::thread_categoriest::const_iterator 
	   t_it = which_threads.thread_categories.begin();
	 t_it != which_threads.thread_categories.end(); ++t_it)
     {
       lock_graph_domaint::nodet node(t_it->first);
       unsigned n = lock_graph.add_node(node);
       current_locks[t_it->first].push_back(n);
     }
   }

  typedef static_analysist<lock_graph_domaint> baset;

  // overloading
  virtual void initialize(const goto_programt &goto_program);
  virtual void initialize(const goto_functionst &goto_functions);

  void detect_deadlocks();

  void output(std::ostream &out);
  void convert(xmlt &dest);
  void convert_node(xmlt &dest,lock_graph_domaint::grapht::node_indext n);
  void convert_edge(xmlt &dest,lock_graph_domaint::grapht::node_indext n,
		    lock_graph_domaint::grapht::node_indext m);
  void output_deadlocks(std::ostream &out);
  void convert_deadlocks(xmlt &dest);

public:

  virtual void generate_state(locationt l);

  lock_set_analysist &lock_set_analysis;
  which_threads_internalt &which_threads;

  lock_graph_domaint::grapht lock_graph;
  lock_graph_domaint::current_lockst current_locks;

  typedef std::list<lock_graph_domaint::grapht::patht> deadlockst;
  deadlockst  potential_deadlocks;

};

#include <util/ui_message.h>

class goto_functionst;
class goto_programt;
class lock_grapht;

void show_lock_graph(
  ui_message_handlert::uit ui,
  const goto_functionst &goto_functions,
  lock_grapht &lock_graph);

void show_deadlocks(
  ui_message_handlert::uit ui,
  const goto_functionst &goto_functions,
  lock_grapht &lock_graph);

#endif
