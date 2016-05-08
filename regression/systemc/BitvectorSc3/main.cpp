#include <cassert>

//#define USE_BV

#define MAX_SIZE 32
#ifdef USE_BV
typedef __CPROVER::unsignedbv<MAX_SIZE> bv_type;
#else
typedef int bv_type;
#endif

void bitvector_assign_to(const bv_type &src,
			 bv_type &dst,
			 int offset,
			 int length)
{
  //TODO: we have to expose the bitvector_extract operator at the interface
  bv_type tmpsrc = src;
  tmpsrc <<= MAX_SIZE-(offset+length);
  tmpsrc >>= MAX_SIZE-length;
  tmpsrc <<= offset;
  bv_type tmpdst1 = dst;
  tmpdst1 >>= offset+length;
  tmpdst1 <<= offset+length;
  bv_type tmpdst2 = dst;
  tmpdst2 <<= MAX_SIZE-length;
  tmpdst2 >>= MAX_SIZE-length;
  dst = tmpdst1 | tmpsrc | tmpdst2;
//  for(int i=0; i<length; ++i);
//    dest[offset+i] = src[i];
}

void bitvector_assign_from(const bv_type &src,
			   int offset,
			   int length,
			   bv_type &dst)
{
  //TODO: we have to expose the bitvector_extract operator at the interface
  dst = src;
  dst <<= offset; //caution: this produces "garbage" beyond the width of dst
}

class sc_uint_subref;

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

  sc_uint_base &operator=(const sc_uint_subref &other)
  {
    //TODO: forward declaration of sc_uint_subref not yet analysed at this point
    //bitvector_assign_from(other.ptr->val,other.ptr->left,other.length(),val);
    return *this;
  }
  
  bool operator==(const sc_uint_base &other)
  {
    return val == other.val;
  }

  sc_uint_base operator += (const sc_uint_base &other)
  {
    val += other.val; 
    return *this;
  }

  sc_uint_subref range(int left, int right)
  {
    //TODO: forward declaration of sc_uint_subref not yet analysed at this point
    return sc_uint_subref(this, left, right);
  }

  int length() const
  {
    return m_len;
  } 

 protected:
  bv_type val;
  const int m_len;
};

template <int W>
class sc_uint : public sc_uint_base
{
 public:
  explicit sc_uint(unsigned long v)
    : sc_uint_base(v, W)
  {
  }

  sc_uint<W> &operator=(const sc_uint &other)
  {
    //TODO: does not convert this correctly
    // sc_uint_base::operator=(other);
    return *this;
  }

  sc_uint<W> &operator=(const sc_uint_subref &other)
  {
    //TODO: does not convert this correctly
    // sc_uint_subref::operator=(other);
    return *this;
  }

  bool operator==(const sc_uint &other)
  {
    return true; //sc_uint_base::operator==(other);
  }

  sc_uint<W> operator += (const sc_uint &other)
  {
    //TODO: does not convert this correctly
    //sc_uint_base::operator+=(other);
    return *this;
  }

};

class sc_uint_subref
{
 friend class sc_uint_base;

 public:
  sc_uint_subref(sc_uint_base *_ptr, int _left, int _right)
    : ptr(_ptr), left(_left), right(_right)
  {}

  sc_uint_base &operator=(const sc_uint_base &other)
  { 
   bitvector_assign_to(other.val, ptr->val,left,other.length());
    return *ptr;
  }

  int length() const
  {
    return right-left;
  } 

 protected:
  sc_uint_base *ptr;
  int left, right;
  
};

int main(int argc, char** argv)
{
  //TODO: declaration alone doesn't type-check
  sc_uint<4> x(15); //1111
  sc_uint<2> y(0);  //00
  sc_uint<2> z(2);  //10
  x.range(0,1) = y; //1100
  y = x.range(1,2); //10

  assert(y == z);

  return 0;
}
