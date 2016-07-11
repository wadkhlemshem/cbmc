#ifndef SYSTEMC_SC_UINT_H
#define SYSTEMC_SC_UINT_H

#include <cassert>
#include "sc_uint_base.h"

#ifndef __CPROVER__
#include <iostream>
#endif

template <int W>
class sc_uint : public sc_uint_base
{
 public:
#ifndef __CPROVER__
  sc_uint() : sc_uint_base(0, W) {}
#else
  sc_uint() : sc_uint_base(0, W)
  {
    bv_type v;
    bv_type max = (((bv_type)1)<<W)-1; //relies on underflow
    __CPROVER_assume(v<=max);
    val = v;
  }
#endif

  sc_uint(unsigned long v)
    : sc_uint_base(v, W)
  {
  }

  sc_uint(const sc_uint_base &b)
    : sc_uint_base(0, W)
  {
    val = b.val;
  }

  sc_uint(const sc_uint_subref &b)
    : sc_uint_base(b)
  {
  }

  sc_uint(const sc_uint_bitref &b)
    : sc_uint_base(b)
  {
  }

  sc_uint<W> &operator=(const sc_uint_base &other)
  {
    sc_uint_base::operator=(other);
    return *this;
  }

  sc_uint<W> &operator=(const sc_uint_subref &other)
  {
    sc_uint_base::operator=(other);
    return *this;
  }
/*
  sc_uint<W> &operator=(unsigned long v)
  {
    this->val = v;
    return *this;
  }
*/
  bool operator==(const sc_uint_base &other) const
  {
    return sc_uint_base::operator==(other);
  }

  sc_uint<W> operator += (const sc_uint_base &other)
  {
    return sc_uint_base::operator+=(other);
  }

  sc_uint<W> operator *= (const sc_uint_base &other)
  {
    return sc_uint_base::operator*=(other);
  }

  sc_uint<W> operator+ (const sc_uint_base &other)
  {
    return sc_uint<W>(sc_uint_base::operator+(other));
  }

  sc_uint<W> operator* (const sc_uint_base &other)
  {
    return sc_uint<W>(sc_uint_base::operator*(other));
  }

  sc_uint<W> operator >>= (int v)
  {
    return sc_uint_base::operator>>=(v);
  }

  sc_uint<W> operator <<= (int v)
  {
    return sc_uint_base::operator<<=(v);
  }

  sc_uint<W> operator~ ()
  {
    return sc_uint_base::operator~();
  }

  sc_uint<W> operator^ (const sc_uint_base &other)
  {
    return sc_uint<W>(sc_uint_base::operator^(other));
  }

  sc_uint<W> operator| (const sc_uint_base &other)
  {
    return sc_uint<W>(sc_uint_base::operator|(other));
  }

  sc_uint<W> operator& (const sc_uint_base &other)
  {
    return sc_uint<W>(sc_uint_base::operator&(other));
  }

};

#ifndef __CPROVER__
template<int W>
std::ostream& operator<<(std::ostream& out,  sc_uint<W> v)
{
  out << v.to_uint();
  return out;
}
#endif

#endif
