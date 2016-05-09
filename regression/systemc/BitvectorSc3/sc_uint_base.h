#ifndef SYSTEMC_SC_UINT_BASE_H
#define SYSTEMC_SC_UINT_BASE_H

#include <cassert>
#include "systemc_util.h"

class sc_uint_subref;
class sc_uint_base;

class sc_uint_subref
{
 friend class sc_uint_base;

 public:
  sc_uint_subref(sc_uint_base *_ptr, int _left, int _right)
    : ptr(_ptr), left(_left), right(_right)
  {}

  sc_uint_base &operator=(const sc_uint_base &other);

  int length() const
  {
    return left-right+1;
  } 

  unsigned int to_uint() const;

 protected:
  sc_uint_base *ptr;
  int left, right;
  
};

class sc_uint_base
{
 friend class sc_uint_subref;

 public:
  explicit sc_uint_base(unsigned long v, int _len)
    : val(v), m_len(_len)
  {
  }

  sc_uint_base &operator=(const sc_uint_base &other)
  {
    val = other.val;
    return *this;
  }

  sc_uint_base &operator=(const sc_uint_subref &other);
  
  bool operator==(const sc_uint_base &other)
  {
    return val == other.val;
  }

  sc_uint_base operator += (const sc_uint_base &other)
  {
    val += other.val; 
    return *this;
  }

  sc_uint_subref range(int left, int right);

  int length() const
  {
    return m_len;
  } 

  unsigned int to_uint() const
  {
    return val;
  }

 protected:
  bv_type val;
  const int m_len;
};

#endif
