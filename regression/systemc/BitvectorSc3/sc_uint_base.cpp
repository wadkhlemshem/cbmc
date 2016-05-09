#include <cassert>
#include "sc_uint_base.h"

sc_uint_base &sc_uint_base::operator=(const sc_uint_subref &other)
{
  //TODO: forward declaration of sc_uint_subref not yet analysed at this point
  bitvector_assign_from(other.ptr->val,other.right,other.length(),val);
  return *this;
}

sc_uint_subref sc_uint_base::range(int left, int right)
{
  //TODO: forward declaration of sc_uint_subref not yet analysed at this point
  return sc_uint_subref(this, left, right);
}

sc_uint_base &sc_uint_subref::operator=(const sc_uint_base &other)
{ 
  bitvector_assign_to(other.val, ptr->val,right,other.length());
  return *ptr;
}

unsigned int sc_uint_subref::to_uint() const
{
  sc_uint_base tmp(0,length());
  bitvector_assign_from(ptr->val,right,length(),tmp.val);
  return tmp.to_uint();
}
