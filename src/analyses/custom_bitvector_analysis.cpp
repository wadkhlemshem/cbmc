/*******************************************************************\

Module: Field-insensitive, location-sensitive bitvector analysis

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include <util/xml_expr.h>
#include <util/simplify_expr.h>
#include <util/prefix.h>
#include <util/expr_util.h>

#include <ansi-c/string_constant.h>
#include <ansi-c/c_types.h>

#include "custom_bitvector_analysis.h"

#include <iostream>

/*******************************************************************\

Function: get_string

  Inputs:

 Outputs:

 Purpose: 

\*******************************************************************/

namespace {
irep_idt get_string(const exprt &string_expr)
{
  if(string_expr.id()==ID_typecast)
    return get_string(to_typecast_expr(string_expr).op());
  else if(string_expr.id()==ID_address_of)
    return get_string(to_address_of_expr(string_expr).object());
  else if(string_expr.id()==ID_index)
    return get_string(to_index_expr(string_expr).array());
  else if(string_expr.id()==ID_string_constant)
    return string_expr.get(ID_value); 
  else
    return irep_idt();
}
}

/*******************************************************************\

Function: custom_bitvector_domaint::set_bit

  Inputs:

 Outputs:

 Purpose: 

\*******************************************************************/

void custom_bitvector_domaint::set_bit(
  const irep_idt &identifier,
  unsigned bit_nr,
  modet mode)
{
  switch(mode)
  {
  case SET_MUST:
    set_bit(must_bits[identifier], bit_nr);
    break;
  
  case CLEAR_MUST:
    clear_bit(must_bits[identifier], bit_nr);
    break;
  
  case SET_MAY:
    set_bit(may_bits[identifier], bit_nr);
    break;
  
  case CLEAR_MAY:
    clear_bit(may_bits[identifier], bit_nr);
    break;
  }
}

/*******************************************************************\

Function: custom_bitvector_domaint::set_bit

  Inputs:

 Outputs:

 Purpose: 

\*******************************************************************/

void custom_bitvector_domaint::set_bit(
  const exprt &lhs,
  unsigned bit_nr,
  modet mode)
{
  irep_idt id=object2id(lhs);
  if(!id.empty()) set_bit(id, bit_nr, mode);
}

/*******************************************************************\

Function: custom_bitvector_domaint::object2id

  Inputs:

 Outputs:

 Purpose: 

\*******************************************************************/

irep_idt custom_bitvector_domaint::object2id(const exprt &src)
{
  if(src.id()==ID_symbol)
  {
    irep_idt identifier=to_symbol_expr(src).get_identifier();
    if(has_prefix(id2string(identifier), "__CPROVER_")) return irep_idt();
    return identifier;
  }
  else if(src.id()==ID_dereference)
  {
    const exprt &op=to_dereference_expr(src).pointer();
    
    if(op.id()==ID_address_of)
    {
      return object2id(to_address_of_expr(op).object());
    }
    else if(op.id()==ID_typecast)
    {
      return object2id(dereference_exprt(to_typecast_expr(op).op()));
    }
    else if(op.id()==ID_plus)
    {
      exprt ptr=nil_exprt();

      forall_operands(it, op)
        if(it->type().id()==ID_pointer) ptr=*it;

      if(ptr.is_nil()) return irep_idt();
      return object2id(dereference_exprt(ptr));
    }
    else
    {
      irep_idt op_id=object2id(op);
      if(op_id.empty())
        return irep_idt();
      else
        return '*'+id2string(op_id);
    }
  }
  else if(src.id()==ID_index)
  {
    if(to_index_expr(src).index().is_zero() &&
       to_index_expr(src).array().id()==ID_string_constant)
      return object2id(to_index_expr(src).array());
    else
      return irep_idt();    
  }
  else if(src.id()==ID_string_constant)
    return "\""+id2string(src.get(ID_value))+"\"";
  else if(src.id()==ID_typecast)
    return object2id(to_typecast_expr(src).op());
  else
    return irep_idt();
}

/*******************************************************************\

Function: custom_bitvector_domaint::assign_lhs

  Inputs:

 Outputs:

 Purpose: 

\*******************************************************************/

void custom_bitvector_domaint::assign_lhs(
  const exprt &lhs,
  const vectorst &vectors)
{
  irep_idt id=object2id(lhs);
  if(!id.empty()) assign_lhs(id, vectors);
}

/*******************************************************************\

Function: custom_bitvector_domaint::assign_lhs

  Inputs:

 Outputs:

 Purpose: 

\*******************************************************************/

void custom_bitvector_domaint::assign_lhs(
  const irep_idt &identifier,
  const vectorst &vectors)
{
  // we erase blank ones to avoid noise

  if(is_empty(vectors.must_bits))
    must_bits.erase(identifier);
  else
    must_bits[identifier]=vectors.must_bits;
  
  if(is_empty(vectors.may_bits))
    may_bits.erase(identifier);
  else
    may_bits[identifier]=vectors.may_bits;
}

/*******************************************************************\

Function: custom_bitvector_domaint::get_rhs

  Inputs:

 Outputs:

 Purpose: 

\*******************************************************************/

custom_bitvector_domaint::vectorst
  custom_bitvector_domaint::get_rhs(const irep_idt &identifier) const
{
  vectorst vectors;

  bitst::const_iterator may_it=may_bits.find(identifier);
  if(may_it!=may_bits.end()) vectors.may_bits=may_it->second;
  
  bitst::const_iterator must_it=must_bits.find(identifier);
  if(must_it!=must_bits.end()) vectors.must_bits=must_it->second;
  
  return vectors;
}

/*******************************************************************\

Function: custom_bitvector_domaint::get_rhs

  Inputs:

 Outputs:

 Purpose: 

\*******************************************************************/

custom_bitvector_domaint::vectorst
  custom_bitvector_domaint::get_rhs(const exprt &rhs) const
{
  if(rhs.id()==ID_symbol ||
     rhs.id()==ID_dereference ||
     rhs.id()==ID_string_constant)
  {
    const irep_idt identifier=object2id(rhs);
    if(!identifier.empty())
      return get_rhs(identifier);
  }
  else if(rhs.id()==ID_typecast)
  {
    return get_rhs(to_typecast_expr(rhs).op());
  }
  else if(rhs.id()==ID_if)
  {
    // need to merge both
    vectorst v_true=get_rhs(to_if_expr(rhs).true_case());
    vectorst v_false=get_rhs(to_if_expr(rhs).false_case());
    return merge(v_true, v_false);
  }
  
  return vectorst();
}

/*******************************************************************\

Function: custom_bitvector_analysist::get_bit_nr

  Inputs:

 Outputs:

 Purpose: 

\*******************************************************************/

unsigned custom_bitvector_analysist::get_bit_nr(
  const exprt &string_expr)
{
  irep_idt s=get_string(string_expr);
  if(s==irep_idt())
    return bits("(unknown)");
  else
    return bits(s);
}

/*******************************************************************\

Function: custom_bitvector_domaint::aliases

  Inputs:

 Outputs:

 Purpose: 

\*******************************************************************/

std::set<exprt> custom_bitvector_analysist::aliases(
  const exprt &src,
  locationt loc)
{
  if(src.id()==ID_symbol)
  {
    std::set<exprt> result;
    result.insert(src);
    return result;
  }
  else if(src.id()==ID_dereference)
  {
    exprt pointer=to_dereference_expr(src).pointer();
  
    std::set<exprt> pointer_set=
      local_may_alias_factory(loc).get(loc, pointer);

    std::set<exprt> result;

    for(std::set<exprt>::const_iterator
        p_it=pointer_set.begin();
        p_it!=pointer_set.end();
        p_it++)
    {
      result.insert(dereference_exprt(*p_it));
    }
    
    result.insert(src);
    
    return result;
  }
  else if(src.id()==ID_typecast)
  {
    return aliases(to_typecast_expr(src).op(), loc);
  }
  else
    return std::set<exprt>();
}

/*******************************************************************\

Function: custom_bitvector_domaint::transform

  Inputs:

 Outputs:

 Purpose: 

\*******************************************************************/

void custom_bitvector_domaint::transform(
  locationt from,
  locationt to,
  ai_baset &ai,
  const namespacet &ns)
{
  // upcast of ai
  custom_bitvector_analysist &cba=
    static_cast<custom_bitvector_analysist &>(ai);

  const goto_programt::instructiont &instruction=*from;

  switch(instruction.type)
  {
  case ASSIGN:
    {
      const code_assignt &code_assign=to_code_assign(instruction.code);

      // We shall ignore assignments of the form *P = ..., because
      // we don't want to override the flags on *P. This way, the flags
      // appear to be attached to the memory location, as opposed
      // to the data at the memory location.
      // We should likely have separate __CPROVER_set_must_memory()
      // or the like for that purpose.
      
      if(code_assign.lhs().id()==ID_dereference)
        break;
      
      // may alias other stuff
      std::set<exprt> lhs_set=cba.aliases(code_assign.lhs(), from);
        
      vectorst rhs_vectors=get_rhs(code_assign.rhs());
      
      for(std::set<exprt>::const_iterator
          l_it=lhs_set.begin(); l_it!=lhs_set.end(); l_it++)
      {
        assign_lhs(*l_it, rhs_vectors);
      }
      
      // is it a pointer?
      if(code_assign.lhs().type().id()==ID_pointer)
      {
        dereference_exprt lhs_deref(code_assign.lhs());
        dereference_exprt rhs_deref(code_assign.rhs());
        vectorst rhs_vectors=get_rhs(rhs_deref);
        assign_lhs(lhs_deref, rhs_vectors);
      }
    }
    break;

  case DECL:
    {
      const code_declt &code_decl=to_code_decl(instruction.code);
      assign_lhs(code_decl.symbol(), vectorst());

      // is it a pointer?
      if(code_decl.symbol().type().id()==ID_pointer)
        assign_lhs(dereference_exprt(code_decl.symbol()), vectorst());
    }
    break;

  case DEAD:
    {
      const code_deadt &code_dead=to_code_dead(instruction.code);
      assign_lhs(code_dead.symbol(), vectorst());

      // is it a pointer?
      if(code_dead.symbol().type().id()==ID_pointer)
        assign_lhs(dereference_exprt(code_dead.symbol()), vectorst());
    }
    break;

  case FUNCTION_CALL:
    {
      const code_function_callt &code_function_call=to_code_function_call(instruction.code);
      const exprt &function=code_function_call.function();
      
      if(function.id()==ID_symbol)
      {
        const irep_idt &identifier=to_symbol_expr(function).get_identifier();

        if(identifier=="__CPROVER_set_must" ||
           identifier=="__CPROVER_clear_must" ||
           identifier=="__CPROVER_set_may" ||
           identifier=="__CPROVER_clear_may")
        {
          if(code_function_call.arguments().size()==2)
          {
            unsigned bit_nr=
              cba.get_bit_nr(code_function_call.arguments()[1]);
              
            modet mode;
            
            if(identifier=="__CPROVER_set_must")
              mode=SET_MUST;
            else if(identifier=="__CPROVER_clear_must")
              mode=CLEAR_MUST;
            else if(identifier=="__CPROVER_set_may")
              mode=SET_MAY;
            else if(identifier=="__CPROVER_clear_may")
              mode=CLEAR_MAY;
            else
              assert(false);
            
            exprt lhs=code_function_call.arguments()[0];
            
            if(lhs.is_constant() &&
               to_constant_expr(lhs).get_value()==ID_NULL) // NULL means all
            {
              if(mode==CLEAR_MAY)
              {
                for(bitst::iterator b_it=may_bits.begin();
                    b_it!=may_bits.end();
                    b_it++)
                  clear_bit(b_it->second, bit_nr);

                // erase blank ones
                erase_blank_vectors(may_bits);
              }
              else if(mode==CLEAR_MUST)
              {
                for(bitst::iterator b_it=must_bits.begin();
                    b_it!=must_bits.end();
                    b_it++)
                  clear_bit(b_it->second, bit_nr);

                // erase blank ones
                erase_blank_vectors(must_bits);
              }
            }
            else
            {
              dereference_exprt deref(lhs);
              
              // may alias other stuff
              std::set<exprt> lhs_set=cba.aliases(deref, from);
              
              for(std::set<exprt>::const_iterator
                  l_it=lhs_set.begin(); l_it!=lhs_set.end(); l_it++)
              {
                set_bit(*l_it, bit_nr, mode);
              }
            }
          }
        }
        else if(identifier=="__CPROVER_event")
        {
          if(code_function_call.arguments().size()>=1)
          {
            irep_idt event=get_string(code_function_call.arguments()[0]);
            if(event=="fopen") // "fopen", filename, mode, fopen_result
            {
              irep_idt filename=get_string(code_function_call.arguments()[1]);
              irep_idt mode=get_string(code_function_call.arguments()[2]);
              
              bool read=false, write=false;
              
              for(std::string::const_iterator m_it=
                  id2string(mode).begin(); m_it!=id2string(mode).end(); m_it++)
                switch(*m_it)
                {
                case 'a':
                case 'x':
                case 'w': write=true; break;
                case 'r': read=true; break;
                case '+': read=write=true; break;
                default:;
                }
              
              dereference_exprt deref(code_function_call.arguments()[3]);
              
              // may alias other stuff
              std::set<exprt> lhs_set=cba.aliases(deref, from);
              
              for(std::set<exprt>::const_iterator
                  l_it=lhs_set.begin(); l_it!=lhs_set.end(); l_it++)
              {
                // we record as "open_mode_filename"
                if(read)
                {
                  unsigned bit_nr=cba.bits(
                    std::string("open_R_"+id2string(filename)));

                  set_bit(*l_it, bit_nr, SET_MAY);
                }

                if(write)
                {
                  unsigned bit_nr=cba.bits(
                    std::string("open_W_"+id2string(filename)));

                  set_bit(*l_it, bit_nr, SET_MAY);
                }
              }
              
            }
            else if(event=="fclose")
            { // "fclose", stream

              dereference_exprt deref(code_function_call.arguments()[1]);
              
              // may alias other stuff
              std::set<exprt> lhs_set=cba.aliases(deref, from);
              
              for(unsigned bit_nr=0; bit_nr<cba.bits.size(); bit_nr++)
              {
                irep_idt flag=cba.bits[bit_nr];
                if(has_prefix(id2string(flag), "open_"))
                {
                  for(std::set<exprt>::const_iterator
                      l_it=lhs_set.begin(); l_it!=lhs_set.end(); l_it++)
                  {
                    set_bit(*l_it, bit_nr, CLEAR_MAY);
                  }
                }
              }
            }
            else if(event=="freopen") // "freopen", filename, mode, f
            {
              // collect filenames attached to 'f' first
              std::set<irep_idt> filenames;

              custom_bitvector_domaint::vectorst v=
                get_rhs(dereference_exprt(code_function_call.arguments()[3]));
          
              for(unsigned bit_nr=0; bit_nr<cba.bits.size(); bit_nr++)
              {
                if(get_bit(v.may_bits, bit_nr))
                {
                  irep_idt flag=cba.bits[bit_nr];
                
                  // we record as "open_mode_filename"
                  if(has_prefix(id2string(flag), "open_W_") ||
                     has_prefix(id2string(flag), "open_R_"))
                  {
                    std::string file=std::string(id2string(flag), 7, std::string::npos);
                    filenames.insert(file);
                  }
                }
              }
              
              // now close 'f'

              dereference_exprt deref(code_function_call.arguments()[3]);
              
              // may alias other stuff
              std::set<exprt> lhs_set=cba.aliases(deref, from);
              
              for(unsigned bit_nr=0; bit_nr<cba.bits.size(); bit_nr++)
              {
                irep_idt flag=cba.bits[bit_nr];
                if(has_prefix(id2string(flag), "open_"))
                {
                  for(std::set<exprt>::const_iterator
                      l_it=lhs_set.begin(); l_it!=lhs_set.end(); l_it++)
                  {
                    set_bit(*l_it, bit_nr, CLEAR_MAY);
                  }
                }
              }
              
              // now check whether there are conflicting files
              
              if(!filenames.empty())
              {
                irep_idt filename=*filenames.begin();
              
                irep_idt mode=get_string(code_function_call.arguments()[2]);
                
                bool read=false, write=false;
                
                for(std::string::const_iterator m_it=
                    id2string(mode).begin(); m_it!=id2string(mode).end(); m_it++)
                  switch(*m_it)
                  {
                  case 'a':
                  case 'x':
                  case 'w': write=true; break;
                  case 'r': read=true; break;
                  case '+': read=write=true; break;
                  default:;
                  }
                  
                bool conflict=false;
                  
                for(bitst::const_iterator b_it=may_bits.begin();
                    b_it!=may_bits.end(); b_it++)
                {
                  for(unsigned bit_nr=0; bit_nr<cba.bits.size(); bit_nr++)
                  {
                    if(get_bit(b_it->second, bit_nr))
                    {
                      irep_idt flag=cba.bits[bit_nr];
                      if(read && flag=="open_W_"+id2string(filename))
                        conflict=true;
                      else if(write && flag=="open_R_"+id2string(filename))
                        conflict=true;
                    }
                  }
                }
                
                // now open up new file
                
                for(std::set<exprt>::const_iterator
                    l_it=lhs_set.begin(); l_it!=lhs_set.end(); l_it++)
                {
                  // we record as "open_mode_filename"
                  if(read)
                  {
                    unsigned bit_nr=cba.bits(
                      std::string("open_R_"+id2string(filename)));

                    set_bit(*l_it, bit_nr, SET_MAY);
                  }

                  if(write)
                  {
                    unsigned bit_nr=cba.bits(
                      std::string("open_W_"+id2string(filename)));

                    set_bit(*l_it, bit_nr, SET_MAY);
                  }

                  // if we have a conflict, set "freopen_same_file_rw"
                  if(conflict)
                  {
                    unsigned bit_nr=cba.bits("freopen_same_file_rw");
                    set_bit(*l_it, bit_nr, SET_MAY);
                  }
                }
              }
              
            }
            else if(event=="invalidate_pointer") // "invalidate_pointer", "flag"
            {
              irep_idt flag=get_string(code_function_call.arguments()[1]);
              unsigned bit_nr_flag=cba.bits(flag);
              unsigned bit_nr_invalidated=cba.bits("invalidated");

              for(bitst::const_iterator b_it=may_bits.begin();
                  b_it!=may_bits.end(); b_it++)
              {
                if(get_bit(b_it->second, bit_nr_flag))
                  set_bit(b_it->first, bit_nr_invalidated, SET_MAY);
              }              
            }
          }
        }
      }
    }
    break;
    
  case GOTO:
    if(has_get_must_or_may(instruction.guard))
    {
      exprt guard=instruction.guard;
    
      if(to!=from->get_target()) guard.make_not();

      exprt result=eval(guard, cba);
      exprt result2=simplify_expr(result, ns);

      if(result2.is_false())
        make_bottom();
    }
    break;

  default:;
  }
}

/*******************************************************************\

Function: custom_bitvector_domaint::output

  Inputs:

 Outputs:

 Purpose: 

\*******************************************************************/

void custom_bitvector_domaint::output(
  std::ostream &out,
  const ai_baset &ai,
  const namespacet &ns) const
{
  if(is_bottom)
    out << "BOTTOM\n";

  const custom_bitvector_analysist &cba=
    static_cast<const custom_bitvector_analysist &>(ai);
    
  for(bitst::const_iterator it=may_bits.begin();
      it!=may_bits.end();
      it++)
  {
    out << it->first << " MAY:";
    
    for(std::size_t b=0; b<it->second.size(); b++)
      if(it->second[b])
        out << ' ' << cba.bits[b];

    out << '\n';
  }

  for(bitst::const_iterator it=must_bits.begin();
      it!=must_bits.end();
      it++)
  {
    out << it->first << " MUST:";

    for(std::size_t b=0; b<it->second.size(); b++)
      if(it->second[b])
        out << ' ' << cba.bits[b];

    out << '\n';
  }
}

/*******************************************************************\

Function: custom_bitvector_domaint::merge

  Inputs:

 Outputs:

 Purpose: 

\*******************************************************************/

bool custom_bitvector_domaint::merge(
  const custom_bitvector_domaint &b,
  locationt from,
  locationt to)
{
  if(b.is_bottom)
    return false; // no change

  if(is_bottom)
  {
    *this=b;
    return true; // change
  }

  bool changed=false;

  // first do MAY
  for(bitst::const_iterator b_it=b.may_bits.begin();
      b_it!=b.may_bits.end();
      b_it++)
  {
    bit_vectort &a_bits=may_bits[b_it->first];
    bit_vectort old=a_bits;
    if(or_vectors(a_bits, b_it->second))
      changed=true;
  }

  // now do MUST
  for(bitst::iterator a_it=must_bits.begin();
      a_it!=must_bits.end();
      a_it++)
  {
    bitst::const_iterator b_it=
      b.must_bits.find(a_it->first);

    if(b_it==b.must_bits.end())
    {
      a_it->second.clear();
      changed=true;
    }
    else
    {
      bit_vectort old=a_it->second;
      if(and_vectors(a_it->second, b_it->second))
        changed=true;
    }
  }
  
  // erase blank ones
  erase_blank_vectors(may_bits);
  erase_blank_vectors(must_bits);

  return changed;
}

/*******************************************************************\

Function: custom_bitvector_domaint::erase_blank_vectors

  Inputs:

 Outputs:

 Purpose: erase blank bitvectors

\*******************************************************************/

void custom_bitvector_domaint::erase_blank_vectors(bitst &bits)
{
  for(bitst::iterator a_it=bits.begin();
      a_it!=bits.end();
      )
  {
    if(is_empty(a_it->second))
      a_it=bits.erase(a_it);
    else
      a_it++;
  }
}

/*******************************************************************\

Function: custom_bitvector_domaint::has_get_must_or_may

  Inputs:

 Outputs:

 Purpose: 

\*******************************************************************/

bool custom_bitvector_domaint::has_get_must_or_may(const exprt &src)
{
  if(src.id()=="get_must" ||
     src.id()=="get_may")
    return true;
  
  forall_operands(it, src)
    if(has_get_must_or_may(*it)) return true;

  return false;
}

/*******************************************************************\

Function: custom_bitvector_domaint::has_predicate

  Inputs:

 Outputs:

 Purpose: 

\*******************************************************************/

bool custom_bitvector_domaint::has_predicate(const exprt &src)
{
  if(src.id()==ID_predicate)
    return true;
  
  forall_operands(it, src)
    if(has_predicate(*it)) return true;

  return false;
}

/*******************************************************************\

Function: custom_bitvector_domaint::has_dereference

  Inputs:

 Outputs:

 Purpose: 

\*******************************************************************/

bool custom_bitvector_domaint::has_dereference(const exprt &src)
{
  if(src.id()==ID_dereference)
    return true;
  
  forall_operands(it, src)
    if(has_dereference(*it)) return true;

  return false;
}

/*******************************************************************\

Function: custom_bitvector_domaint::eval

  Inputs:

 Outputs:

 Purpose: 

\*******************************************************************/

exprt custom_bitvector_domaint::eval(
  const exprt &src,
  custom_bitvector_analysist &cba) const
{
  if(src.id()=="get_must" || src.id()=="get_may")
  {
    if(src.operands().size()==2)
    {
      unsigned bit_nr=
        cba.get_bit_nr(src.op1());

      exprt pointer=src.op0();
      
      if(pointer.is_constant() &&
         to_constant_expr(pointer).get_value()==ID_NULL) // NULL means all
      {
        if(src.id()=="get_may")
        {
          for(custom_bitvector_domaint::bitst::const_iterator
              b_it=may_bits.begin();
              b_it!=may_bits.end();
              b_it++)
          {
            if(get_bit(b_it->second, bit_nr)) return true_exprt();
          }
          
          return false_exprt();
        }
        else if(src.id()=="get_must")
        {
          return false_exprt();
        }
        else
          return src;
      }
      else
      {
        custom_bitvector_domaint::vectorst v=
          get_rhs(dereference_exprt(pointer));

        bool value=false;

        if(src.id()=="get_must")
          value=get_bit(v.must_bits, bit_nr);
        else if(src.id()=="get_may")
          value=get_bit(v.may_bits, bit_nr);

        if(value)
          return true_exprt();
        else
          return false_exprt();
      }
    }
    else
      return src;
  }
  else if(src.id()==ID_predicate)
  {
    if(src.operands().size()>=1)
    {
      irep_idt p=get_string(src.op0());
      if(p=="same_file_rw") // "same_file_rw", filename, mode
      {
        irep_idt filename=get_string(src.op1());
        irep_idt mode=get_string(src.op2());
        
        bool read=false, write=false;
        
        for(std::string::const_iterator m_it=
            id2string(mode).begin(); m_it!=id2string(mode).end(); m_it++)
          switch(*m_it)
          {
          case 'a':
          case 'x':
          case 'w': write=true; break;
          case 'r': read=true; break;
          case '+': read=write=true; break;
          default:;
          }
        
        for(bitst::const_iterator b_it=may_bits.begin();
            b_it!=may_bits.end(); b_it++)
        {
          for(unsigned bit_nr=0; bit_nr<cba.bits.size(); bit_nr++)
          {
            if(get_bit(b_it->second, bit_nr))
            {
              irep_idt flag=cba.bits[bit_nr];
              if(read && flag=="open_W_"+id2string(filename))
                return false_exprt();
              else if(write && flag=="open_R_"+id2string(filename))
                return false_exprt();
            }
          }
        }
        
        return true_exprt();
      }
      else if(p=="freopen_same_file_rw") // "freopen_same_file_rw", f
      {
        custom_bitvector_domaint::vectorst v=
          get_rhs(dereference_exprt(src.op1()));

        unsigned bit_nr=cba.bits("freopen_same_file_rw");

        if(get_bit(v.may_bits, bit_nr))
          return false_exprt();
        else
          return true_exprt();
      }
      else
        return src;
    }
    else
      return src;
  }
  else
  {
    exprt tmp=src;
    Forall_operands(it, tmp)
      *it=eval(*it, cba);
  
    return tmp;
  }
}

/*******************************************************************\

Function: custom_bitvector_domaint::check_dereference

  Inputs:

 Outputs:

 Purpose: 

\*******************************************************************/

bool custom_bitvector_domaint::check_dereference(
  const exprt &src,
  custom_bitvector_analysist &cba) const
{
  if(!has_dereference(src))
    return true;

  if(src.id()==ID_dereference)
  {
    custom_bitvector_domaint::vectorst v=get_rhs(src);

    unsigned bit_nr=cba.bits("invalidated");

    if(get_bit(v.may_bits, bit_nr))
      return false;
    else
      return true;
  }
  else 
  {
    forall_operands(it, src)
      if(!check_dereference(*it, cba))
        return false;
    
    return true;
  }
}

/*******************************************************************\

Function: custom_bitvector_analysist::instrument

  Inputs:

 Outputs:

 Purpose: 

\*******************************************************************/

void custom_bitvector_analysist::instrument(goto_functionst &)
{
}

/*******************************************************************\

Function: custom_bitvector_analysist::check

  Inputs:

 Outputs:

 Purpose: 

\*******************************************************************/

void custom_bitvector_analysist::check(
  const namespacet &ns,
  const goto_functionst &goto_functions,
  bool use_xml,
  std::ostream &out)
{
  unsigned pass=0, fail=0, unknown=0;
  
  forall_goto_functions(f_it, goto_functions)
  {
    //if(!f_it->second.body.has_assertion()) continue;
    
    if(f_it->first=="__actual_thread_spawn" ||
       // f_it->first=="_start" ||
       has_prefix(id2string(f_it->first), "__CPROVER_"))
      continue;

    if(!use_xml)
      out << "******** Function " << f_it->first << '\n';

    forall_goto_program_instructions(i_it, f_it->second.body)
    {
      exprt result;
      irep_idt description;

      if(i_it->is_assign() ||
         i_it->is_other())
      {
        if(!custom_bitvector_domaint::has_dereference(i_it->code))
          continue;

        bool tmp=operator[](i_it).check_dereference(i_it->code, *this);
        
        if(tmp)
          result=true_exprt();
        else
          result=false_exprt();
          
        description="pointer invalidated";
      }
      else if(i_it->is_function_call())
      {
        // we'll even complain about just passing an invalidated pointer
        code_function_callt c=to_code_function_call(i_it->code);
        
        if(c.function().id()==ID_symbol &&
           has_prefix(id2string(to_symbol_expr(c.function()).get_identifier()), "__CPROVER_"))
          continue;

        exprt tmp1;
        tmp1.operands()=c.arguments();
        bool found=false;
        Forall_operands(it, tmp1)
          if(it->type().id()==ID_pointer)
          {
            *it=dereference_exprt(*it);
            found=true;
          }

        if(!found) continue;

        bool tmp2=operator[](i_it).check_dereference(tmp1, *this);
      
        if(tmp2)
          result=true_exprt();
        else
          result=false_exprt();
        
        description="pointer invalidated";        
      }
      else if(i_it->is_assert())
      {
        if(!custom_bitvector_domaint::has_get_must_or_may(i_it->guard) &&
           !custom_bitvector_domaint::has_predicate(i_it->guard))
          continue;

        if(operator[](i_it).is_bottom) continue;

        exprt tmp=eval(i_it->guard, i_it);
        result=simplify_expr(tmp, ns);
        
        description=i_it->source_location.get_comment();
      }
      else
        continue;

      if(use_xml)
      {
        out << "<result status=\"";
        if(result.is_true())
          out << "SUCCESS";
        else if(result.is_false())
          out << "FAILURE";
        else 
          out << "UNKNOWN";
        out << "\">\n";
        out << xml(i_it->source_location);
        out << "<description>"
            << description
            << "</description>\n";
        out << "</result>\n\n";
      }
      else
      {
        out << i_it->source_location;
        if(!description.empty())
          out << ", " << description;
        out << ": ";
        out << from_expr(ns, f_it->first, result);
        out << '\n';
      }

      if(result.is_true())
        pass++;
      else if(result.is_false())
        fail++;
      else
        unknown++;
    }

    if(!use_xml)
      out << '\n';
  }
  
  if(!use_xml)
    out << "SUMMARY: " << pass << " pass, " << fail << " fail, "
        << unknown << " unknown\n";
}
