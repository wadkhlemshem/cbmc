/*******************************************************************\

Module: graph visitor for computing edges involved for fencing

Author: Vincent Nimal

\*******************************************************************/

/// \file
/// graph visitor for computing edges involved for fencing

#ifndef CPROVER_MUSKETEER_GRAPH_VISITOR_H
#define CPROVER_MUSKETEER_GRAPH_VISITOR_H

#include <set>
#include <list>

#include <goto-instrument/wmm/event_graph.h>

class fence_insertert;

class const_graph_visitort
{
protected:
  typedef event_grapht::critical_cyclet::delayt edget;

  fence_insertert &fence_inserter;
  std::set<event_idt> visited_nodes;

public:
  /* computes the PT (btwn), CT (cml) and IT (cntrl) */
  void PT(const edget &e, std::set<unsigned> &edges);
  void CT(const edget &e, std::set<unsigned> &edges);
  void CT_not_powr(const edget &e, std::set<unsigned> &edges);
  void IT(const edget &e, std::set<unsigned> &edges);

  void const_graph_explore(
    event_grapht &graph,
    event_idt next,
    event_idt end,
    std::list<event_idt> &old_path);
  void graph_explore(event_grapht &graph, event_idt next, event_idt end,
    std::list<event_idt> &old_path, std::set<unsigned> &edges);
  void graph_explore_BC(event_grapht &egraph, event_idt next,
    std::list<event_idt> &old_path, std::set<unsigned> &edges, bool porw);
  void graph_explore_AC(event_grapht &egraph, event_idt next,
    std::list<event_idt> &old_path, std::set<unsigned> &edges, bool porw);
  void graph_explore_BC(
    event_grapht &egraph, event_idt next,
    std::list<event_idt> &old_path,
    std::set<unsigned> &edges)
  {
    graph_explore_BC(egraph, next, old_path, edges, false);
  }

  void graph_explore_AC(
    event_grapht &egraph,
    event_idt next,
    std::list<event_idt> &old_path,
    std::set<unsigned> &edges)
  {
    graph_explore_AC(egraph, next, old_path, edges, false);
  }

  void const_graph_explore_BC(event_grapht &egraph, event_idt next,
    std::list<event_idt> &old_path);
  void const_graph_explore_AC(event_grapht &egraph, event_idt next,
    std::list<event_idt> &old_path);

  explicit const_graph_visitort(fence_insertert &_fence_inserter)
    : fence_inserter(_fence_inserter)
  {}
};

#endif // CPROVER_MUSKETEER_GRAPH_VISITOR_H
