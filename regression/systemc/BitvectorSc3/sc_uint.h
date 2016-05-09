#ifndef SYSTEMC_SC_UINT_H
#define SYSTEMC_SC_UINT_H

#include <cassert>
#include "sc_uint_base.h"

template <int W>
class sc_uint : public sc_uint_base
{
 public:
  explicit sc_uint(unsigned long v)
    : sc_uint_base(v, W)
  {
  }

  sc_uint<W> &operator=(const sc_uint_base &other)
  {
    //TODO: does not convert this correctly
    sc_uint_base::operator=(other);
    return *this;
  }

  sc_uint<W> &operator=(const sc_uint_subref &other)
  {
    //TODO: does not convert this correctly
    sc_uint_base::operator=(other);
    return *this;
  }

  bool operator==(const sc_uint_base &other)
  {
    return sc_uint_base::operator==(other);
  }

  sc_uint<W> operator += (const sc_uint_base &other)
  {
    //TODO: does not convert this correctly
    return sc_uint_base::operator+=(other);
  }

};

#endif
