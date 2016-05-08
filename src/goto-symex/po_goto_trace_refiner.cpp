/*******************************************************************\

Module: Traces of GOTO Programs, specialised to shared R/W events

Author: Daniel Kroening, Peter Schrammel


\*******************************************************************/

#include <cassert>
#include <iostream>
#include <langapi/language_util.h>

#include <util/threeval.h>
#include <util/simplify_expr.h>
#include <util/arith_tools.h>

#include <solvers/prop/prop_conv.h>
#include <solvers/prop/prop.h>

#include "po_goto_trace_refiner.h"

/*******************************************************************\

Function: po_goto_trace_refinert::operator()(

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void po_goto_trace_refinert::operator()(prop_convt &prop_conv)
{
  goto_tracet goto_trace;
  goto_trace_SSA_step_mapt steps_map;
  partial_order_concurrencyt::choice_mapt choice_map;
  choice_map = memory_model.get_choice_map();

  build_po_goto_trace(equation,prop_conv,ns,choice_map,goto_trace,steps_map);

  memory_model(equation,goto_trace,steps_map);

#if 0
  unsigned old_nb_SSA_steps = equation.count_converted_SSA_steps();
#endif

  equation.convert_constraints(prop_conv);

#if 0
  std::cout << (equation.count_converted_SSA_steps()-old_nb_SSA_steps) << " steps converted" << std::endl;
#endif
}

/*******************************************************************\

Function: po_goto_trace_refinert::build_po_goto_trace

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void po_goto_trace_refinert::build_po_goto_trace(
  const symex_target_equationt &target,
  symex_target_equationt::SSA_stepst::const_iterator end_step,
  const prop_convt &prop_conv,
  const namespacet &ns,
  const partial_order_concurrencyt::choice_mapt &choice_map,
  goto_tracet &goto_trace,
  goto_trace_SSA_step_mapt &steps_map)
{
  // Get additional reads and writes from choices
  typedef std::set<irep_idt> additional_eventst;
  additional_eventst additional_reads, additional_writes;
  for(partial_order_concurrencyt::choice_mapt::const_iterator
	it = choice_map.begin(); it != choice_map.end(); ++it)
  {
    if(prop_conv.get(it->first) == true_exprt())
    {
#if 0
      std::cout << "additional read: " << it->second.first << std::endl;
      std::cout << "additional write: " << it->second.second << std::endl;
#endif      
      additional_reads.insert(it->second.first);
      additional_writes.insert(it->second.second);
    }
  }
  
  // We need to re-sort the steps according to their clock.
  // Furthermore, read-events need to occur before write
  // events with the same clock.
  
  typedef std::map<mp_integer, goto_tracet::stepst> time_mapt;
  time_mapt time_map;
  typedef std::list<symex_target_equationt::SSA_stepst::const_iterator>
    SSA_steps_listt;
  SSA_steps_listt ssa_steps_list;
  typedef std::map<mp_integer, SSA_steps_listt>  time_map_ssat;
  time_map_ssat time_map_ssa;
  
  mp_integer current_time=0;
  
  for(symex_target_equationt::SSA_stepst::const_iterator
      it=target.SSA_steps.begin();
      it!=end_step;
      ++it)
  {
    const symex_target_equationt::SSA_stept &SSA_step=*it;

#if 0 // we cannot do that because don't care guards
      //    may have a 'false' value assigned
    if(prop_conv.l_get(SSA_step.guard_literal)==tvt(false))
      continue;
#endif
    if(prop_conv.l_get(SSA_step.guard_literal)!=tvt(true))
    {
      if(!((it->is_shared_read() &&
	  additional_reads.find(
	    to_symbol_expr(SSA_step.ssa_lhs).get_identifier()) 
	      != additional_reads.end()) ||
	 (it->is_shared_write() &&
	  additional_writes.find(
	    to_symbol_expr(SSA_step.ssa_lhs).get_identifier())
	      != additional_writes.end())))
        continue;
#if 1
      else
      {
	if(it->is_shared_read()) std::cout << "additional read: "; 
	if(it->is_shared_write()) std::cout << "additional write: ";
	std::cout << to_symbol_expr(SSA_step.ssa_lhs).get_identifier() << std::endl;
      }
#endif    
    }
    
    if(it->is_constraint() ||
       it->is_spawn())
      continue;
    else if(it->is_atomic_begin())
    {
      // for atomic sections the timing can only be determined once we see
      // a shared read or write (if there is none, the time will be
      // reverted to the time before entering the atomic section); we thus
      // use a temporary negative time slot to gather all events
      current_time*=-1;
      continue;
    }
    else if(it->is_shared_read() || it->is_shared_write() ||
            it->is_atomic_end())
    {
      mp_integer time_before=current_time;

      if(it->is_shared_read() || it->is_shared_write())
      {
        // these are just used to get the time stamp
        exprt clock_value=prop_conv.get(
          symbol_exprt(partial_order_concurrencyt::rw_clock_id(it)));
#if 0
	std::cout << "clock_value: " << from_expr(ns,"",clock_value)
		  << std::endl;
#endif
	// in lazy encoding this might have no value
        to_integer(clock_value, current_time);
      }
      else if(it->is_atomic_end() && current_time<0)
        current_time*=-1;

#if 0
      std::cout << "time_before: " << time_before << std::endl;
      std::cout << "current_time: " << current_time << std::endl;
#endif
      assert(current_time>=0);
      // TODO: not sure whether this is the right action
      //if(current_time<0) 
      //  continue;

      // move any steps gathered in an atomic section

      if(time_before<0)
      {
        time_mapt::iterator entry=
          time_map.insert(std::make_pair(
              current_time,
              goto_tracet::stepst())).first;
        entry->second.splice(entry->second.end(), time_map[time_before]);
        time_map.erase(time_before);
        time_map_ssat::iterator entry_ssa =
          time_map_ssa.insert(std::make_pair(
              current_time,
              SSA_steps_listt())).first;
        entry_ssa->second.splice(entry_ssa->second.end(), 
				 time_map_ssa[time_before]);
        time_map_ssa.erase(time_before);
      }

//      continue;
    }
    
    // drop everything except assertions
    if(!(it->is_assert() || it->is_shared_read() || it->is_shared_write()))
      continue;

#if 0
    SSA_step.output(ns,std::cout);
#endif

    goto_tracet::stepst &steps=time_map[current_time];
    steps.push_back(goto_trace_stept());    
    goto_trace_stept &goto_trace_step=steps.back();
    SSA_steps_listt &steps_ssa=time_map_ssa[current_time];
    steps_ssa.push_back(it); 

    
#if 0
    if(it->is_assignment() &&
       (SSA_step.assignment_type==symex_target_equationt::PHI ||
        SSA_step.assignment_type==symex_target_equationt::GUARD))
      continue;

    goto_tracet::stepst &steps=time_map[current_time];
    steps.push_back(goto_trace_stept());    
    goto_trace_stept &goto_trace_step=steps.back();
    SSA_steps_listt &steps_ssa=time_map_ssa[current_time];
    steps_ssa.push_back(it); 
    
    goto_trace_step.thread_nr=SSA_step.source.thread_nr;
    goto_trace_step.pc=SSA_step.source.pc;
    goto_trace_step.comment=SSA_step.comment;
    goto_trace_step.lhs_object=SSA_step.original_lhs_object;
    goto_trace_step.type=SSA_step.type;
    goto_trace_step.hidden=SSA_step.hidden;
    goto_trace_step.format_string=SSA_step.format_string;
    goto_trace_step.io_id=SSA_step.io_id;
    goto_trace_step.formatted=SSA_step.formatted;
    goto_trace_step.identifier=SSA_step.identifier;

    goto_trace_step.assignment_type=
      (SSA_step.assignment_type==symex_targett::VISIBLE_ACTUAL_PARAMETER ||
       SSA_step.assignment_type==symex_targett::HIDDEN_ACTUAL_PARAMETER)?
      goto_trace_stept::ACTUAL_PARAMETER:
      goto_trace_stept::STATE;

    if(SSA_step.original_full_lhs.is_not_nil())
      goto_trace_step.full_lhs=
        build_full_lhs_rec(
          prop_conv, ns, SSA_step.original_full_lhs, SSA_step.ssa_full_lhs);
    
    if(SSA_step.ssa_lhs.is_not_nil())
      goto_trace_step.lhs_object_value=prop_conv.get(SSA_step.ssa_lhs);
    
    if(SSA_step.ssa_full_lhs.is_not_nil())
    {
      goto_trace_step.full_lhs_value=prop_conv.get(SSA_step.ssa_full_lhs);
      simplify(goto_trace_step.full_lhs_value, ns);
    }
    
    for(std::list<exprt>::const_iterator
        j=SSA_step.converted_io_args.begin();
        j!=SSA_step.converted_io_args.end();
        j++)
    {
      const exprt &arg=*j;
      if(arg.is_constant() ||
         arg.id()==ID_string_constant)
        goto_trace_step.io_args.push_back(arg);
      else
      {
        exprt tmp=prop_conv.get(arg);
        goto_trace_step.io_args.push_back(tmp);
      }
    }
#endif

    if(SSA_step.is_assert() ||
       SSA_step.is_assume())
    {
      goto_trace_step.cond_expr=SSA_step.cond_expr;

      goto_trace_step.cond_value=
        prop_conv.l_get(SSA_step.cond_literal).is_true();
    }
    else if(SSA_step.is_location() &&
            SSA_step.source.pc->is_goto())
    {
      goto_trace_step.cond_expr=SSA_step.source.pc->guard;

      const bool backwards=SSA_step.source.pc->is_backwards_goto();

      symex_target_equationt::SSA_stepst::const_iterator next=it;
      ++next;
      assert(next!=target.SSA_steps.end());

      // goto was taken if backwards and next is enabled or forward
      // and next is not active;
      // there is an ambiguity here if a forward goto is to the next
      // instruction, which we simply ignore for now
      goto_trace_step.goto_taken=
        backwards==
        (prop_conv.l_get(next->guard_literal)==tvt(true));
    }
  }
  
  // Now assemble into a single goto_trace.
  // This expoits sorted-ness of the map.
  time_map_ssat::iterator ts_it=time_map_ssa.begin();
  for(time_mapt::iterator t_it=time_map.begin();
      t_it!=time_map.end(); ++t_it, ++ts_it)
  {
    goto_trace.steps.splice(goto_trace.steps.end(), t_it->second);
    ssa_steps_list.splice(ssa_steps_list.end(), ts_it->second);  
  }

  assert(goto_trace.steps.size() == ssa_steps_list.size());
  steps_map.reserve(goto_trace.steps.size());

  // produce the step numbers
  unsigned step_nr=0;
  SSA_steps_listt::iterator ss_it = ssa_steps_list.begin();
  for(goto_tracet::stepst::iterator
      s_it=goto_trace.steps.begin();
      s_it!=goto_trace.steps.end();
      ++s_it, ++ss_it)
  {
    s_it->step_nr=++step_nr;
    steps_map.push_back(*ss_it);
  }
}

/*******************************************************************\

Function: po_goto_trace_refinert::build_po_goto_trace

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void po_goto_trace_refinert::build_po_goto_trace(
  const symex_target_equationt &target,
  const prop_convt &prop_conv,
  const namespacet &ns,
  const partial_order_concurrencyt::choice_mapt &choice_map,
  goto_tracet &goto_trace,
  goto_trace_SSA_step_mapt &steps_map)
{
  build_po_goto_trace(
    target, target.SSA_steps.end(), prop_conv, ns,
    choice_map,
    goto_trace, steps_map);

  // Now delete anything after first failed assertion
  for(goto_tracet::stepst::iterator
      s_it1=goto_trace.steps.begin();
      s_it1!=goto_trace.steps.end();
      s_it1++)
    if(s_it1->is_assert() && !s_it1->cond_value)
    {
      s_it1++;

      for(goto_tracet::stepst::iterator
          s_it2=s_it1;
          s_it2!=goto_trace.steps.end();
          s_it2=goto_trace.steps.erase(s_it2));
        
      break;
    }
}

