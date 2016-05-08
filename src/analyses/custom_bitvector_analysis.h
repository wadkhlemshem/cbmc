/*******************************************************************\

Module: Field-insensitive, location-sensitive bitvector analysis

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#ifndef CPROVER_CUSTOM_BITVECTOR_ANALYSIS_H
#define CPROVER_CUSTOM_BITVECTOR_ANALYSIS_H

#include <util/numbering.h>

#include "ai.h"
#include "local_may_alias.h"

/*******************************************************************\

   Class: custom_bitvector_domaint
   
 Purpose:

\*******************************************************************/

class custom_bitvector_analysist;

class custom_bitvector_domaint:public ai_domain_baset
{
public:
  virtual void transform(
    locationt from,
    locationt to,
    ai_baset &ai,
    const namespacet &ns);

  virtual void output(
    std::ostream &out,
    const ai_baset &ai,
    const namespacet &ns) const;

  virtual void make_bottom()
  {
    may_bits.clear();
    must_bits.clear();
    is_bottom=true;
  }

  virtual void make_top()
  {
    may_bits.clear();
    must_bits.clear();
    is_bottom=false;
  }

  bool merge(
    const custom_bitvector_domaint &b,
    locationt from,
    locationt to);

  typedef std::vector<bool> bit_vectort;
  
  typedef std::map<irep_idt, bit_vectort> bitst;
  
  struct vectorst
  {
    bit_vectort may_bits, must_bits;
  };
  
  static bool or_vectors(bit_vectort &dest, const bit_vectort &src)
  {
    bool changed=false;
    if(src.size()>dest.size()) dest.resize(src.size());
    for(unsigned i=0; i<src.size(); i++)
      if(src[i] && !dest[i]) { dest[i]=true; changed=true; }
    return changed;
  }  
  
  static bool and_vectors(bit_vectort &dest, const bit_vectort &src)
  {
    bool changed=false;
    if(src.size()>dest.size()) dest.resize(src.size());
    for(unsigned i=0; i<dest.size(); i++)
      if(dest[i] && (src.size()<=i || !src[i])) { dest[i]=false; changed=true; }
    return changed;
  }  
  
  static vectorst merge(const vectorst &a, const vectorst &b)
  {
    vectorst result;
    result.may_bits=a.may_bits;
    or_vectors(result.may_bits, b.may_bits);
    result.must_bits=a.must_bits;
    and_vectors(result.must_bits, b.must_bits);
    return result;
  }
  
  static bool is_empty(const bit_vectort &v)
  {
    for(const auto b : v)
      if(b) return false;

    return true;
  }
  
  bitst may_bits, must_bits;
  
  void assign_lhs(const exprt &, const vectorst &);
  void assign_lhs(const irep_idt &, const vectorst &);
  vectorst get_rhs(const exprt &) const;
  vectorst get_rhs(const irep_idt &) const;

  bool is_bottom;
  
  custom_bitvector_domaint():is_bottom(true)
  {
  }

  static bool has_get_must_or_may(const exprt &);
  static bool has_predicate(const exprt &);
  static bool has_dereference(const exprt &);

  exprt eval(
    const exprt &,
    custom_bitvector_analysist &) const;
  
  bool check_dereference(
    const exprt &,
    custom_bitvector_analysist &) const;

protected:  
  typedef enum { SET_MUST, CLEAR_MUST, SET_MAY, CLEAR_MAY } modet;

  void set_bit(const exprt &, unsigned bit_nr, modet);
  void set_bit(const irep_idt &, unsigned bit_nr, modet);

  static inline void set_bit(bit_vectort &dest, unsigned bit_nr)
  {
    if(dest.size()<=bit_nr) dest.resize(bit_nr+1);
    dest[bit_nr]=1;
  }
  
  static inline void clear_bit(bit_vectort &dest, unsigned bit_nr)
  {
    if(dest.size()<=bit_nr) return;
    dest[bit_nr]=0;
  }  
  
  static inline bool get_bit(const bit_vectort src, unsigned bit_nr)
  {
    if(src.size()<=bit_nr) return false;
    return src[bit_nr];
  }
  
  void erase_blank_vectors(bitst &);  
  
  static irep_idt object2id(const exprt &);
};

class custom_bitvector_analysist:public ait<custom_bitvector_domaint> 
{
public:
  void instrument(goto_functionst &);
  void check(const namespacet &, const goto_functionst &, bool xml, std::ostream &);

  exprt eval(const exprt &src, locationt loc)
  {
    return operator[](loc).eval(src, *this);
  }

  unsigned get_bit_nr(const exprt &);

  typedef numbering<irep_idt> bitst;
  bitst bits;
  
protected:
  virtual void initialize(const goto_functionst &_goto_functions)
  {
    local_may_alias_factory(_goto_functions);
  }

  friend class custom_bitvector_domaint;

  local_may_alias_factoryt local_may_alias_factory;
  
  std::set<exprt> aliases(const exprt &, locationt loc);
};

#endif
