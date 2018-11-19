/* FUNCTION: fabs */

inline double fabs(double d) { return __CPROVER_fabs(d); }

/* FUNCTION: fabsl */

inline long double fabsl(long double d) { return __CPROVER_fabsl(d); }

/* FUNCTION: fabsf */

inline float fabsf(float f) { return __CPROVER_fabsf(f); }

/* FUNCTION: __builtin_fabs */

inline double __builtin_fabs(double d) { return __CPROVER_fabs(d); }

/* FUNCTION: __builtin_fabsl */

inline long double __builtin_fabsl(long double d) { return __CPROVER_fabsl(d); }

/* FUNCTION: __builtin_fabsf */

inline float __builtin_fabsf(float f) { return __CPROVER_fabsf(f); }

/* FUNCTION: __CPROVER_isgreaterf */

int __CPROVER_isgreaterf(float f, float g) { return f > g; }

/* FUNCTION: __CPROVER_isgreaterd */

int __CPROVER_isgreaterd(double f, double g) { return f > g; }

/* FUNCTION: __CPROVER_isgreaterequalf */

int __CPROVER_isgreaterequalf(float f, float g) { return f >= g; }

/* FUNCTION: __CPROVER_isgreaterequald */

int __CPROVER_isgreaterequald(double f, double g) { return f >= g; }

/* FUNCTION: __CPROVER_islessf */

int __CPROVER_islessf(float f, float g) { return f < g;}

/* FUNCTION: __CPROVER_islessd */

int __CPROVER_islessd(double f, double g) { return f < g;}

/* FUNCTION: __CPROVER_islessequalf */

int __CPROVER_islessequalf(float f, float g) { return f <= g; }

/* FUNCTION: __CPROVER_islessequald */

int __CPROVER_islessequald(double f, double g) { return f <= g; }

/* FUNCTION: __CPROVER_islessgreaterf */

int __CPROVER_islessgreaterf(float f, float g) { return (f < g) || (f > g); }

/* FUNCTION: __CPROVER_islessgreaterd */

int __CPROVER_islessgreaterd(double f, double g) { return (f < g) || (f > g); }

/* FUNCTION: __CPROVER_isunorderedf */

int __CPROVER_isunorderedf(float f, float g)
{
  return __CPROVER_isnanf(f) || __CPROVER_isnanf(g);
}

/* FUNCTION: __CPROVER_isunorderedd */

int __CPROVER_isunorderedd(double f, double g)
{
  return __CPROVER_isnand(f) || __CPROVER_isnand(g);
}

/* FUNCTION: isfinite */

#undef isfinite

int isfinite(double d) { return __CPROVER_isfinited(d); }

/* FUNCTION: __finite */

int __finite(double d) { return __CPROVER_isfinited(d); }

/* FUNCTION: __finitef */

int __finitef(float f) { return __CPROVER_isfinitef(f); }

/* FUNCTION: __finitel */

int __finitel(long double ld) { return __CPROVER_isfiniteld(ld); }

/* FUNCTION: isinf */

#undef isinf

inline int isinf(double d) { return __CPROVER_isinfd(d); }

/* FUNCTION: __isinf */

inline int __isinf(double d) { return __CPROVER_isinfd(d); }

/* FUNCTION: isinff */

inline int isinff(float f) { return __CPROVER_isinff(f); }

/* FUNCTION: __isinff */

inline int __isinff(float f) { return __CPROVER_isinff(f); }

/* FUNCTION: isinfl */

inline int isinfl(long double ld) { return __CPROVER_isinfld(ld); }

/* FUNCTION: __isinfl */

inline int __isinfl(long double ld) { return __CPROVER_isinfld(ld); }

/* FUNCTION: isnan */

#undef isnan

inline int isnan(double d) { return __CPROVER_isnand(d); }

/* FUNCTION: __isnan */

inline int __isnan(double d) { return __CPROVER_isnand(d); }

/* FUNCTION: __isnanf */

inline int __isnanf(float f) { return __CPROVER_isnanf(f); }

/* FUNCTION: isnanf */

inline int isnanf(float f) { return __CPROVER_isnanf(f); }

/* FUNCTION: isnanl */

inline int isnanl(long double ld) { return __CPROVER_isnanld(ld); }

/* FUNCTION: __isnanl */

inline int __isnanl(long double ld) { return __CPROVER_isnanld(ld); }

/* FUNCTION: isnormal */

#undef isnormal

inline int isnormal(double d) { return __CPROVER_isnormald(d); }

/* FUNCTION: __isnormalf */

inline int __isnormalf(float f) { return __CPROVER_isnormalf(f); }

/* FUNCTION: __builtin_inff */

inline float __builtin_inff(void) { return 1.0f/0.0f; }

/* FUNCTION: __builtin_inf */

inline double __builtin_inf(void) { return 1.0/0.0; }

/* FUNCTION: __builtin_infl */

inline long double __builtin_infl(void) { return 1.0l/0.0l; }

/* FUNCTION: __builtin_isinf */

inline int __builtin_isinf(double d) { return __CPROVER_isinfd(d); }

/* FUNCTION: __builtin_isinff */

inline int __builtin_isinff(float f) { return __CPROVER_isinff(f); }

/* FUNCTION: __builtin_isinf */

inline int __builtin_isinfl(long double ld) { return __CPROVER_isinfld(ld); }

/* FUNCTION: __builtin_isnan */

inline int __builtin_isnan(double d) { return __CPROVER_isnand(d); }

/* FUNCTION: __builtin_isnanf */

inline int __builtin_isnanf(float f) { return __CPROVER_isnanf(f); }

/* FUNCTION: __builtin_huge_valf */

inline float __builtin_huge_valf(void) { return 1.0f/0.0f; }

/* FUNCTION: __builtin_huge_val */

inline double __builtin_huge_val(void) { return 1.0/0.0; }

/* FUNCTION: __builtin_huge_vall */

inline long double __builtin_huge_vall(void) { return 1.0l/0.0l; }

/* FUNCTION: _dsign */

inline int _dsign(double d) { return __CPROVER_signd(d); }

/* FUNCTION: _ldsign */

inline int _ldsign(long double ld) { return __CPROVER_signld(ld); }

/* FUNCTION: _fdsign */

inline int _fdsign(float f) { return __CPROVER_signf(f); }

/* FUNCTION: signbit */

#undef signbit

inline int signbit(double d) { return __CPROVER_signd(d); }

/* FUNCTION: __signbitd */

inline int __signbitd(double d) { return __CPROVER_signd(d); }

/* FUNCTION: __signbitf */

inline int __signbitf(float f) { return __CPROVER_signf(f); }

/* FUNCTION: __signbit */

inline int __signbit(double ld) { return __CPROVER_signld(ld); }

/* FUNCTION: _dclass */

#ifndef __CPROVER_MATH_H_INCLUDED
#include <math.h>
#define __CPROVER_MATH_H_INCLUDED
#endif

inline short _dclass(double d) {
  __CPROVER_HIDE:
  return __CPROVER_isnand(d)?FP_NAN:
         __CPROVER_isinfd(d)?FP_INFINITE:
         d==0?FP_ZERO:
         __CPROVER_isnormald(d)?FP_NORMAL:
         FP_SUBNORMAL;
}

/* FUNCTION: _ldclass */

#ifndef __CPROVER_MATH_H_INCLUDED
#include <math.h>
#define __CPROVER_MATH_H_INCLUDED
#endif

inline short _ldclass(long double ld) {
  __CPROVER_HIDE:
  return __CPROVER_isnanld(ld)?FP_NAN:
         __CPROVER_isinfld(ld)?FP_INFINITE:
         ld==0?FP_ZERO:
         __CPROVER_isnormalld(ld)?FP_NORMAL:
         FP_SUBNORMAL;
}

/* FUNCTION: _fdclass */

#ifndef __CPROVER_MATH_H_INCLUDED
#include <math.h>
#define __CPROVER_MATH_H_INCLUDED
#endif

inline short _fdclass(float f) {
  __CPROVER_HIDE:
  return __CPROVER_isnanf(f)?FP_NAN:
         __CPROVER_isinff(f)?FP_INFINITE:
         f==0?FP_ZERO:
         __CPROVER_isnormalf(f)?FP_NORMAL:
         FP_SUBNORMAL;
}

/* FUNCTION: __fpclassifyd */

#ifndef __CPROVER_MATH_H_INCLUDED
#include <math.h>
#define __CPROVER_MATH_H_INCLUDED
#endif

inline int __fpclassifyd(double d) {
  __CPROVER_HIDE:
    return __CPROVER_fpclassify(
      FP_NAN, FP_INFINITE, FP_NORMAL, FP_SUBNORMAL, FP_ZERO, d);
}

/* FUNCTION: __fpclassifyf */

#ifndef __CPROVER_MATH_H_INCLUDED
#include <math.h>
#define __CPROVER_MATH_H_INCLUDED
#endif

inline int __fpclassifyf(float f) {
  __CPROVER_HIDE:
    return __CPROVER_fpclassify(
      FP_NAN, FP_INFINITE, FP_NORMAL, FP_SUBNORMAL, FP_ZERO, f);
}

/* FUNCTION: __fpclassifyl */

#ifndef __CPROVER_MATH_H_INCLUDED
#include <math.h>
#define __CPROVER_MATH_H_INCLUDED
#endif

inline int __fpclassifyl(long double f) {
  __CPROVER_HIDE:
    return __CPROVER_fpclassify(
      FP_NAN, FP_INFINITE, FP_NORMAL, FP_SUBNORMAL, FP_ZERO, f);
}

/* FUNCTION: __fpclassify */

#ifndef __CPROVER_MATH_H_INCLUDED
#include <math.h>
#define __CPROVER_MATH_H_INCLUDED
#endif

// The variant with long double below is needed for older Macs
// only; newer ones use __fpclassifyd.

#ifdef __APPLE__
inline int __fpclassify(long double d) {
  __CPROVER_HIDE:
    return __CPROVER_fpclassify(
      FP_NAN, FP_INFINITE, FP_NORMAL, FP_SUBNORMAL, FP_ZERO, d);
}
#else
inline int __fpclassify(double d) {
  __CPROVER_HIDE:
    return __CPROVER_fpclassify(
      FP_NAN, FP_INFINITE, FP_NORMAL, FP_SUBNORMAL, FP_ZERO, d);
}
#endif

/* FUNCTION: sin */

#ifndef __CPROVER_MATH_H_INCLUDED
#include <math.h>
#define __CPROVER_MATH_H_INCLUDED
#endif


/*
 * ====================================================
 * Copyright (C) 1993 by Sun Microsystems, Inc. All rights reserved.
 *
 * Developed at SunSoft, a Sun Microsystems, Inc. business.
 * Permission to use, copy, modify, and distribute this
 * software is freely granted, provided that this notice 
 * is preserved.
 * ====================================================
 */

#ifdef __LITTLE_ENDIAN
#define __HI(x) *(1+(int*)&x)
#define __LO(x) *(int*)&x
#else
#define __HI(x) *(int*)&x
#define __LO(x) *(1+(int*)&x)
#endif

/* __kernel_sin( x, y, iy)
 * kernel sin function on [-pi/4, pi/4], pi/4 ~ 0.7854
 * Input x is assumed to be bounded by ~pi/4 in magnitude.
 * Input y is the tail of x.
 * Input iy indicates whether y is 0. (if iy=0, y assume to be 0). 
 *
 * Algorithm
 *	1. Since sin(-x) = -sin(x), we need only to consider positive x. 
 *	2. if x < 2^-27 (hx<0x3e400000 0), return x with inexact if x!=0.
 *	3. sin(x) is approximated by a polynomial of degree 13 on
 *	   [0,pi/4]
 *		  	         3            13
 *	   	sin(x) ~ x + S1*x + ... + S6*x
 *	   where
 *	
 * 	|sin(x)         2     4     6     8     10     12  |     -58
 * 	|----- - (1+S1*x +S2*x +S3*x +S4*x +S5*x  +S6*x   )| <= 2
 * 	|  x 					           | 
 * 
 *	4. sin(x+y) = sin(x) + sin'(x')*y
 *		    ~ sin(x) + (1-x*x/2)*y
 *	   For better accuracy, let 
 *		     3      2      2      2      2
 *		r = x *(S2+x *(S3+x *(S4+x *(S5+x *S6))))
 *	   then                   3    2
 *		sin(x) = x + (S1*x + (x *(r-y/2)+y))
 */

double fdlibm_kernel_sin(double x, double y, int iy)
{
  const double 
  half =  5.00000000000000000000e-01, /* 0x3FE00000, 0x00000000 */
  S1  = -1.66666666666666324348e-01, /* 0xBFC55555, 0x55555549 */
  S2  =  8.33333333332248946124e-03, /* 0x3F811111, 0x1110F8A6 */
  S3  = -1.98412698298579493134e-04, /* 0xBF2A01A0, 0x19C161D5 */
  S4  =  2.75573137070700676789e-06, /* 0x3EC71DE3, 0x57B1FE7D */
  S5  = -2.50507602534068634195e-08, /* 0xBE5AE5E6, 0x8A2B9CEB */
  S6  =  1.58969099521155010221e-10; /* 0x3DE5D93A, 0x5ACFD57C */
	double z,r,v;
	int ix;
	ix = __HI(x)&0x7fffffff;	/* high word of x */
	if(ix<0x3e400000)			/* |x| < 2**-27 */
	   {if((int)x==0) return x;}		/* generate inexact */
	z	=  x*x;
	v	=  z*x;
	r	=  S2+z*(S3+z*(S4+z*(S5+z*S6)));
	if(iy==0) return x+v*(S1+z*r);
	else      return x-((z*(half*y-v*r)-y)-v*S1);
}

/*
 * __kernel_cos( x,  y )
 * kernel cos function on [-pi/4, pi/4], pi/4 ~ 0.785398164
 * Input x is assumed to be bounded by ~pi/4 in magnitude.
 * Input y is the tail of x. 
 *
 * Algorithm
 *	1. Since cos(-x) = cos(x), we need only to consider positive x.
 *	2. if x < 2^-27 (hx<0x3e400000 0), return 1 with inexact if x!=0.
 *	3. cos(x) is approximated by a polynomial of degree 14 on
 *	   [0,pi/4]
 *		  	                 4            14
 *	   	cos(x) ~ 1 - x*x/2 + C1*x + ... + C6*x
 *	   where the remez error is
 *	
 * 	|              2     4     6     8     10    12     14 |     -58
 * 	|cos(x)-(1-.5*x +C1*x +C2*x +C3*x +C4*x +C5*x  +C6*x  )| <= 2
 * 	|    					               | 
 * 
 * 	               4     6     8     10    12     14 
 *	4. let r = C1*x +C2*x +C3*x +C4*x +C5*x  +C6*x  , then
 *	       cos(x) = 1 - x*x/2 + r
 *	   since cos(x+y) ~ cos(x) - sin(x)*y 
 *			  ~ cos(x) - x*y,
 *	   a correction term is necessary in cos(x) and hence
 *		cos(x+y) = 1 - (x*x/2 - (r - x*y))
 *	   For better accuracy when x > 0.3, let qx = |x|/4 with
 *	   the last 32 bits mask off, and if x > 0.78125, let qx = 0.28125.
 *	   Then
 *		cos(x+y) = (1-qx) - ((x*x/2-qx) - (r-x*y)).
 *	   Note that 1-qx and (x*x/2-qx) is EXACT here, and the
 *	   magnitude of the latter is at least a quarter of x*x/2,
 *	   thus, reducing the rounding error in the subtraction.
 */

double fdlibm_kernel_cos(double x, double y)
{
  const double 
  one =  1.00000000000000000000e+00, /* 0x3FF00000, 0x00000000 */
  C1  =  4.16666666666666019037e-02, /* 0x3FA55555, 0x5555554C */
  C2  = -1.38888888888741095749e-03, /* 0xBF56C16C, 0x16C15177 */
  C3  =  2.48015872894767294178e-05, /* 0x3EFA01A0, 0x19CB1590 */
  C4  = -2.75573143513906633035e-07, /* 0xBE927E4F, 0x809C52AD */
  C5  =  2.08757232129817482790e-09, /* 0x3E21EE9E, 0xBDB4B1C4 */
  C6  = -1.13596475577881948265e-11; /* 0xBDA8FAE9, 0xBE8838D4 */
	double a,hz,z,r,qx;
	int ix;
	ix = __HI(x)&0x7fffffff;	/* ix = |x|'s high word*/
	if(ix<0x3e400000) {			/* if x < 2**27 */
	    if(((int)x)==0) return one;		/* generate inexact */
	}
	z  = x*x;
	r  = z*(C1+z*(C2+z*(C3+z*(C4+z*(C5+z*C6)))));
	if(ix < 0x3FD33333) 			/* if |x| < 0.3 */ 
	    return one - (0.5*z - (z*r - x*y));
	else {
	    if(ix > 0x3fe90000) {		/* x > 0.78125 */
		qx = 0.28125;
	    } else {
	        __HI(qx) = ix-0x00200000;	/* x/4 */
	        __LO(qx) = 0;
	    }
	    hz = 0.5*z-qx;
	    a  = one-qx;
	    return a - (hz - (z*r-x*y));
	}
}

/* __ieee754_rem_pio2(x,y)
 * 
 * return the remainder of x rem pi/2 in y[0]+y[1]
 * use __kernel_rem_pio2()
 */
// an approximation of __ieee754_rem_pio2
int fdlibm_ieee754_rem_pio2_approx(double x, double *y)
{
  return fmod(x, M_PI_2);
}

/* sin(x)
 * Return sine function of x.
 *
 * kernel function:
 *	__kernel_sin		... sine function on [-pi/4,pi/4]
 *	__kernel_cos		... cose function on [-pi/4,pi/4]
 *	__ieee754_rem_pio2	... argument reduction routine
 *
 * Method.
 *      Let S,C and T denote the sin, cos and tan respectively on 
 *	[-PI/4, +PI/4]. Reduce the argument x to y1+y2 = x-k*pi/2 
 *	in [-pi/4 , +pi/4], and let n = k mod 4.
 *	We have
 *
 *          n        sin(x)      cos(x)        tan(x)
 *     ----------------------------------------------------------
 *	    0	       S	   C		 T
 *	    1	       C	  -S		-1/T
 *	    2	      -S	  -C		 T
 *	    3	      -C	   S		-1/T
 *     ----------------------------------------------------------
 *
 * Special cases:
 *      Let trig be any of sin, cos, or tan.
 *      trig(+-INF)  is NaN, with signals;
 *      trig(NaN)    is that NaN;
 *
 * Accuracy:
 *	TRIG(x) returns trig(x) nearly rounded 
 */

double fdlibm_sin(double x)
{
	double y[2],z=0.0;
	int n, ix;

    /* High word of x. */
	ix = __HI(x);

    /* |x| ~< pi/4 */
	ix &= 0x7fffffff;
	if(ix <= 0x3fe921fb) return fdlibm_kernel_sin(x,z,0);

    /* sin(Inf or NaN) is NaN */
	else if (ix>=0x7ff00000) return x-x;

    /* argument reduction needed */
	else {
    x = fmod(x + M_PI, M_PI * 2) - M_PI; // restrict x so that -M_PI < x < M_PI
n = fdlibm_ieee754_rem_pio2_approx(x,y);
	    switch(n&3) {
		case 0: return  fdlibm_kernel_sin(y[0],y[1],1);
		case 1: return  fdlibm_kernel_cos(y[0],y[1]);
		case 2: return -fdlibm_kernel_sin(y[0],y[1],1);
		default:
			return -fdlibm_kernel_cos(y[0],y[1]);
	    }
	}
}

double sin(double x)
{
  return fdlibm_sin(x);
  //return cos(x - M_PI_2);
}

/* FUNCTION: sinl */

#ifndef __CPROVER_MATH_H_INCLUDED
#include <math.h>
#define __CPROVER_MATH_H_INCLUDED
#endif

long double __VERIFIER_nondet_long_double();

long double sinl(long double x)
{
  return cosl(x - M_PI_2);
}

/* FUNCTION: sinf */

#ifndef __CPROVER_MATH_H_INCLUDED
#include <math.h>
#define __CPROVER_MATH_H_INCLUDED
#endif

float __VERIFIER_nondet_float();

float sinf(float x)
{
  return cosf(x - M_PI_2);
}

/* FUNCTION: cos */

#ifndef __CPROVER_MATH_H_INCLUDED
#include <math.h>
#define __CPROVER_MATH_H_INCLUDED
#endif

double __VERIFIER_nondet_double();

double cos(double x)
{
  return sin(x + M_PI_2);
/*
  double t, s;
  int p;
  p = 0;
  s = 1.0;
  t = 1.0;
  x = fmod(x + M_PI, M_PI * 2) - M_PI; // restrict x so that -M_PI < x < M_PI
  double xsqr = x * x;
  double ab = 1;
  while((ab > 1e-16) && (p < 15))
  {
    p++;
    t = (-t * xsqr) / (((p << 1) - 1) * (p << 1));
    s += t;
    ab = (s == 0) ? 1 : fabs(t / s);
  }
  return s;*/
}

/* FUNCTION: cosl */

#ifndef __CPROVER_MATH_H_INCLUDED
#include <math.h>
#define __CPROVER_MATH_H_INCLUDED
#endif

long double __VERIFIER_nondet_long_double();

long double cosl(long double x)
{
  long double t, s;
  int p;
  p = 0;
  s = 1.0;
  t = 1.0;
  x = fmod(x + M_PI, M_PI * 2) - M_PI; // restrict x so that -M_PI < x < M_PI
  long double xsqr = x * x;
  long double ab = 1;
  while((ab > 1e-16) && (p < 15))
  {
    p++;
    t = (-t * xsqr) / (((p << 1) - 1) * (p << 1));
    s += t;
    ab = (s == 0) ? 1 : fabs(t / s);
  }
  return s;
}

/* FUNCTION: cosf */

#ifndef __CPROVER_MATH_H_INCLUDED
#include <math.h>
#define __CPROVER_MATH_H_INCLUDED
#endif

float __VERIFIER_nondet_float();

float cosf(float x)
{
  float t, s;
  int p;
  p = 0;
  s = 1.0;
  t = 1.0;
  x = fmod(x + M_PI, M_PI * 2) - M_PI; // restrict x so that -M_PI < x < M_PI
  float xsqr = x * x;
  float ab = 1;
  while((ab > 1e-16) && (p < 15))
  {
    p++;
    t = (-t * xsqr) / (((p << 1) - 1) * (p << 1));
    s += t;
    ab = (s == 0) ? 1 : fabs(t / s);
  }
  return s;
}

/* FUNCTION: __builtin_nan */

double __builtin_nan(const char *str)
{
  // the 'str' argument is not yet used
__CPROVER_hide:;
  (void)*str;
  return 0.0/0.0;
}

/* FUNCTION: __builtin_nanf */

float __builtin_nanf(const char *str)
{
  // the 'str' argument is not yet used
__CPROVER_hide:;
  (void)*str;
  return 0.0f/0.0f;
}


/* ISO 9899:2011
 * The call nan("n-char-sequence") is equivalent to
 * strtod("NAN(n-char-sequence)", (char**) NULL); the call nan("") is
 * equivalent to strtod("NAN()", (char**) NULL). If tagp does not
 * point to an n-char sequence or an empty string, the call is
 * equivalent to strtod("NAN", (char**) NULL). Calls to nanf and nanl
 * are equivalent to the corresponding calls to strtof and strtold.
 *
 * The nan functions return a quiet NaN, if available, with content
 * indicated through tagp. If the implementation does not support
 * quiet NaNs, the functions return zero.
 */

/* FUNCTION: nan */

double nan(const char *str) {
  // the 'str' argument is not yet used
 __CPROVER_hide:;
  (void)*str;
  return 0.0/0.0;
}

/* FUNCTION: nanf */

float nanf(const char *str) {
  // the 'str' argument is not yet used
 __CPROVER_hide:;
  (void)*str;
  return 0.0f/0.0f;
}

/* FUNCTION: nanl */

long double nanl(const char *str) {
  // the 'str' argument is not yet used
 __CPROVER_hide:;
  (void)*str;
  return 0.0/0.0;
}

/* FUNCTION: nextUpf */

#ifndef __CPROVER_LIMITS_H_INCLUDED
#include <limits.h>
#define __CPROVER_LIMITS_H_INCLUDED
#endif


// IEEE_754 2008 althought similar to C's nextafter / nexttowards
// Loosely assumes that float is (IEEE-754) binary32

union mixf
{
  float f;
  #ifdef LIBRARY_CHECK
  int bv;
  #else
  __CPROVER_bitvector[CHAR_BIT * sizeof(float)] bv;
  #endif
};

float nextUpf(float f)
{
__CPROVER_hide:;
  if (__CPROVER_isnanf(f))
    return 0.0f/0.0f;  // NaN
  else if (f == 0.0f)
    return 0x1p-149f;
  else if (f > 0.0f)
  {
    if (__CPROVER_isinff(f))
      return f;

    union mixf m;
    m.f = f;
    ++m.bv;
    return m.f;
  }
  else
  {
    //assert(f < 0.0f);

    union mixf m;
    m.f = f;
    --m.bv;
    return m.f;
  }
}

/* FUNCTION: nextUp */

#ifndef __CPROVER_LIMITS_H_INCLUDED
#include <limits.h>
#define __CPROVER_LIMITS_H_INCLUDED
#endif


// IEEE_754 2008 althought similar to C's nextafter / nexttowards
// Loosely assumes that double is (IEEE-754) binary64

union mixd
{
  double f;
  #ifdef LIBRARY_CHECK
  long long int bv;
  #else
  __CPROVER_bitvector[CHAR_BIT * sizeof(double)] bv;
  #endif
};

double nextUp(double d)
{
__CPROVER_hide:;
  if (__CPROVER_isnand(d))
    return 0.0/0.0;  // NaN
  else if (d == 0.0)
    return 0x1.0p-1074;
  else if (d > 0.0)
  {
    if (__CPROVER_isinfd(d))
      return d;

    union mixd m;
    m.f = d;
    ++m.bv;
    return m.f;
  }
  else
  {
    //assert(d < 0.0);

    union mixd m;
    m.f = d;
    --m.bv;
    return m.f;
  }
}


/* FUNCTION: nextUpl */

#ifndef __CPROVER_LIMITS_H_INCLUDED
#include <limits.h>
#define __CPROVER_LIMITS_H_INCLUDED
#endif

// IEEE_754 2008 althought similar to C's nextafter / nexttowards

union mixl
{
  long double f;
  #ifdef LIBRARY_CHECK
  long long int bv;
  #else
  __CPROVER_bitvector[CHAR_BIT * sizeof(long double)] bv;
  #endif
};

long double nextUpl(long double d)
{
__CPROVER_hide:;
  if(__CPROVER_isnanld(d))
    return 0.0/0.0;  // NaN
  else if (d == 0.0)
  {
    union mixl m;
    m.bv = 0x1;
    return m.f;
  }
  else if (d > 0.0)
  {
    if(__CPROVER_isinfld(d))
      return d;

    union mixl m;
    m.f = d;
    ++m.bv;
    return m.f;
  }
  else
  {
    //assert(d < 0.0);

    union mixl m;
    m.f = d;
    --m.bv;
    return m.f;
  }
  
}




/* FUNCTION: sqrtf */

/* This code is *WRONG* in some circumstances, specifically:
 *
 *   1. If run with a rounding mode other than RNE the
 *      answer will be out by one or two ULP.  This could be fixed
 *      with careful choice of round mode for the multiplications.
 *
 *   2. Subnormals have the unusual property that there are
 *      multiple numbers that square to give them.  I.E. if
 *      f is subnormal then there are multiple f1 != f2 such that
 *      f1 * f1 == f == f2 * f2.  This code will return *a*
 *      square root of a subnormal input but not necessarily *the*
 *      square root (i.e. the real value of the square root rounded).
 */

#ifndef __CPROVER_MATH_H_INCLUDED
#include <math.h>
#define __CPROVER_MATH_H_INCLUDED
#endif

#ifndef __CPROVER_FENV_H_INCLUDED
#include <fenv.h>
#define __CPROVER_FENV_H_INCLUDED
#endif

float nextUpf(float f);

float __VERIFIER_nondet_float();

float sqrtf(float f)
{
 __CPROVER_hide:;

  if ( f < 0.0f )
    return 0.0f/0.0f; // NaN
  else if (__CPROVER_isinff(f) ||   // +Inf only
           f == 0.0f          ||   // Includes -0
           __CPROVER_isnanf(f))
    return f;
  else if (__CPROVER_isnormalf(f))
  {
    float lower=__VERIFIER_nondet_float();
    __CPROVER_assume(lower > 0.0f);
    __CPROVER_assume(__CPROVER_isnormalf(lower));
    // Tighter bounds can be given but are dependent on the
    // number of exponent and significand bits.  Thus they are
    // given implicitly...

    float lowerSquare = lower * lower;
    __CPROVER_assume(__CPROVER_isnormalf(lowerSquare));

    float upper = nextUpf(lower);
    float upperSquare = upper * upper;  // Might be +Inf

    // Restrict these to bound f and thus compute the possible
    // values for the square root.  Note that the lower bound
    // can be equal, this is important to catch edge cases such as
    // 0x1.fffffep+127f and relies on the smallest normal number
    // being a perfect square (which it will be for any sensible
    // bit width).
    __CPROVER_assume(lowerSquare <= f);
    __CPROVER_assume(f < upperSquare);

    // Select between them to work out which to return
    switch(fegetround())
    {
    case FE_TONEAREST :
      return (f - lowerSquare < upperSquare - f) ? lower : upper; break;
    case FE_UPWARD :
      return (f - lowerSquare == 0.0f) ? lower : upper; break;
    case FE_DOWNWARD : // Fall through
    case FE_TOWARDZERO :
      return (f - lowerSquare == 0.0f) ? lower : upper; break;
    default:;
      //assert(0);
    }

  }
  else
  {
    //assert(fpclassify(f) == FP_SUBNORMAL);
    //assert(f > 0.0f);

    // With respect to the algebra of floating point number
    // all subnormals seem to be perfect squares, thus ...

    float root=__VERIFIER_nondet_float();
    __CPROVER_assume(root >= 0.0f);

    __CPROVER_assume(root * root == f);

    return root;
  }
}




/* FUNCTION: sqrt */

/* The same caveats as sqrtf apply */

#ifndef __CPROVER_MATH_H_INCLUDED
#include <math.h>
#define __CPROVER_MATH_H_INCLUDED
#endif

#ifndef __CPROVER_FENV_H_INCLUDED
#include <fenv.h>
#define __CPROVER_FENV_H_INCLUDED
#endif

double nextUp(double d);

double __VERIFIER_nondet_double();

double sqrt(double d)
{
 __CPROVER_hide:;

  if ( d < 0.0 )
    return 0.0/0.0; // NaN
  else if (__CPROVER_isinfd(d) ||   // +Inf only
           d == 0.0            ||   // Includes -0
           __CPROVER_isnand(d))
    return d;
  else if (__CPROVER_isnormald(d))
  {
    double lower=__VERIFIER_nondet_double();
    __CPROVER_assume(lower > 0.0);
    __CPROVER_assume(__CPROVER_isnormald(lower));

    double lowerSquare = lower * lower;
    __CPROVER_assume(__CPROVER_isnormald(lowerSquare));

    double upper = nextUp(lower);
    double upperSquare = upper * upper;  // Might be +Inf

    __CPROVER_assume(lowerSquare <= d);
    __CPROVER_assume(d < upperSquare);

    switch(fegetround())
    {
    case FE_TONEAREST:
      return (d - lowerSquare < upperSquare - d) ? lower : upper; break;
    case FE_UPWARD:
      return (d - lowerSquare == 0.0f) ? lower : upper; break;
    case FE_DOWNWARD: // Fall through
    case FE_TOWARDZERO:
      return (d - lowerSquare == 0.0) ? lower : upper; break;
    default:;
      //assert(0);
    }

  }
  else
  {
    //assert(fpclassify(d) == FP_SUBNORMAL);
    //assert(d > 0.0);

    double root=__VERIFIER_nondet_double();
    __CPROVER_assume(root >= 0.0);

    __CPROVER_assume(root * root == d);

    return root;
  }
}

/* FUNCTION: sqrtl */

/* The same caveats as sqrtf apply */

#ifndef __CPROVER_MATH_H_INCLUDED
#include <math.h>
#define __CPROVER_MATH_H_INCLUDED
#endif

#ifndef __CPROVER_FENV_H_INCLUDED
#include <fenv.h>
#define __CPROVER_FENV_H_INCLUDED
#endif

long double nextUpl(long double d);

long double __VERIFIER_nondet_long_double();

long double sqrtl(long double d)
{
 __CPROVER_hide:;

  if(d < 0.0l)
    return 0.0l/0.0l; // NaN
  else if (__CPROVER_isinfld(d) ||   // +Inf only
           d == 0.0l            ||   // Includes -0
           __CPROVER_isnanld(d))
    return d;
  else if (__CPROVER_isnormalld(d))
  {
    long double lower=__VERIFIER_nondet_long_double();
    __CPROVER_assume(lower > 0.0l);
    __CPROVER_assume(__CPROVER_isnormalld(lower));

    long double lowerSquare = lower * lower;
    __CPROVER_assume(__CPROVER_isnormalld(lowerSquare));

    long double upper = nextUpl(lower);
    long double upperSquare = upper * upper;  // Might be +Inf

    __CPROVER_assume(lowerSquare <= d);
    __CPROVER_assume(d < upperSquare);

    switch(fegetround())
    {
    case FE_TONEAREST:
      return (d - lowerSquare < upperSquare - d) ? lower : upper; break;
    case FE_UPWARD:
      return (d - lowerSquare == 0.0l) ? lower : upper; break;
    case FE_DOWNWARD: // Fall through
    case FE_TOWARDZERO:
      return (d - lowerSquare == 0.0l) ? lower : upper; break;
    default:;
      //assert(0);
    }

  }
  else
  {
    //assert(fpclassify(d) == FP_SUBNORMAL);
    //assert(d > 0.0l);

    long double root=__VERIFIER_nondet_long_double();
    __CPROVER_assume(root >= 0.0l);

    __CPROVER_assume(root * root == d);

    return root;
  }
}


/* ISO 9899:2011
 * The fmax functions determine the maximum numeric value of their
 * arguments. 242)
 *
 * 242) NaN arguments are treated as missing data: if one argument is
 * a NaN and the other numeric, then the fmax functions choose the
 * numeric value. See F.10.9.2.
 *
 * - If just one argument is a NaN, the fmax functions return the other
 *   argument (if both arguments are NaNs, the functions return a NaN).
 * - The returned value is exact and is independent of the current
 *   rounding direction mode.
 * - The body of the fmax function might be 374)
 *       { return (isgreaterequal(x, y) || isnan(y)) ? x : y; }
 *
 * 374) Ideally, fmax would be sensitive to the sign of zero, for
 * example fmax(-0.0, +0.0) would return +0; however, implementation
 * in software might be impractical.
 */

/* FUNCTION: fmax */

#ifndef __CPROVER_MATH_H_INCLUDED
#include <math.h>
#define __CPROVER_MATH_H_INCLUDED
#endif

// TODO : Should call a __CPROVER_function so that it can be converted to SMT-LIB
double fmax(double f, double g) { return ((f >= g) || isnan(g)) ? f : g; }

/* FUNCTION : fmaxf */

#ifndef __CPROVER_MATH_H_INCLUDED
#include <math.h>
#define __CPROVER_MATH_H_INCLUDED
#endif

// TODO : Should call a __CPROVER_function so that it can be converted to SMT-LIB
float fmaxf(float f, float g) { return ((f >= g) || isnan(g)) ? f : g; }


/* FUNCTION : fmaxl */

#ifndef __CPROVER_MATH_H_INCLUDED
#include <math.h>
#define __CPROVER_MATH_H_INCLUDED
#endif

// TODO : Should call a __CPROVER_function so that it can be converted to SMT-LIB
long double fmaxl(long double f, long double g) { return ((f >= g) || isnan(g)) ? f : g; }


/* ISO 9899:2011
 * The fmin functions determine the minimum numeric value of their
 * arguments.243)
 *
 * 243) The fmin functions are analogous to the fmax functions in
 * their treatment of NaNs.
 *
 * - The fmin functions are analogous to the fmax functions (see F.10.9.2).
 * - The returned value is exact and is independent of the current
 *   rounding direction mode.
 */

/* FUNCTION: fmin */

#ifndef __CPROVER_MATH_H_INCLUDED
#include <math.h>
#define __CPROVER_MATH_H_INCLUDED
#endif
 
// TODO : Should call a __CPROVER_function so that it can be converted to SMT-LIB
double fmin(double f, double g) { return ((f <= g) || isnan(g)) ? f : g; }

/* FUNCTION: fminf */

#ifndef __CPROVER_MATH_H_INCLUDED
#include <math.h>
#define __CPROVER_MATH_H_INCLUDED
#endif

// TODO : Should call a __CPROVER_function so that it can be converted to SMT-LIB 
float fminf(float f, float g) { return ((f <= g) || isnan(g)) ? f : g; }

/* FUNCTION: fminl */

#ifndef __CPROVER_MATH_H_INCLUDED
#include <math.h>
#define __CPROVER_MATH_H_INCLUDED
#endif

// TODO : Should call a __CPROVER_function so that it can be converted to SMT-LIB 
long double fminl(long double f, long double g) { return ((f <= g) || isnan(g)) ? f : g; }


/* ISO 9899:2011
 * The fdim functions determine the positive difference between their
 * arguments:
 *     x - y if x > y
 *     +0    if x <= y
 * A range error may occur.
 */

/* FUNCTION: fdim */

#ifndef __CPROVER_MATH_H_INCLUDED
#include <math.h>
#define __CPROVER_MATH_H_INCLUDED
#endif

double fdim(double f, double g) { return ((f > g) ? f - g : +0.0); }


/* FUNCTION: fdimf */

#ifndef __CPROVER_MATH_H_INCLUDED
#include <math.h>
#define __CPROVER_MATH_H_INCLUDED
#endif

float fdimf(float f, float g) { return ((f > g) ? f - g : +0.0f); }


/* FUNCTION: fdiml */

#ifndef __CPROVER_MATH_H_INCLUDED
#include <math.h>
#define __CPROVER_MATH_H_INCLUDED
#endif

long double fdiml(long double f, long double g) { return ((f > g) ? f - g : +0.0); }



/* FUNCTION: __sort_of_CPROVER_round_to_integral */
// TODO : Should be a real __CPROVER function to convert to SMT-LIB

#ifndef __CPROVER_MATH_H_INCLUDED
#include <math.h>
#define __CPROVER_MATH_H_INCLUDED
#endif

#ifndef __CPROVER_FENV_H_INCLUDED
#include <fenv.h>
#define __CPROVER_FENV_H_INCLUDED
#endif

double __sort_of_CPROVER_round_to_integral (int rounding_mode, double d)
{
  double magicConst = 0x1.0p+52;
  double return_value;
  int saved_rounding_mode = fegetround();
  fesetround(rounding_mode);
  
  if (fabs(d) >= magicConst || d == 0.0)
  {
    return_value = d;
  }
  else
  {
    if (!signbit(d)) {
      double tmp = d + magicConst;
      return_value = tmp - magicConst;
    } else {
      double tmp = d - magicConst;
      return_value = tmp + magicConst;    
    }
  }

  fesetround(saved_rounding_mode);
  return return_value;
}

/* FUNCTION: __sort_of_CPROVER_round_to_integralf */
// TODO : Should be a real __CPROVER function to convert to SMT-LIB

#ifndef __CPROVER_MATH_H_INCLUDED
#include <math.h>
#define __CPROVER_MATH_H_INCLUDED
#endif

#ifndef __CPROVER_FENV_H_INCLUDED
#include <fenv.h>
#define __CPROVER_FENV_H_INCLUDED
#endif

float __sort_of_CPROVER_round_to_integralf (int rounding_mode, float d)
{
  float magicConst = 0x1.0p+23f;  // 23 is significant
  float return_value;
  int saved_rounding_mode = fegetround();
  fesetround(rounding_mode);
  
  if (fabsf(d) >= magicConst || d == 0.0)
  {
    return_value = d;
  }
  else
  {
    if (!signbit(d)) {
      float tmp = d + magicConst;
      return_value = tmp - magicConst;    
    } else {
      float tmp = d - magicConst;
      return_value = tmp + magicConst;    
    }
  }

  fesetround(saved_rounding_mode);
  return return_value;
}


/* FUNCTION: __sort_of_CPROVER_round_to_integrall */
// TODO : Should be a real __CPROVER function to convert to SMT-LIB

#ifndef __CPROVER_MATH_H_INCLUDED
#include <math.h>
#define __CPROVER_MATH_H_INCLUDED
#endif

#ifndef __CPROVER_FENV_H_INCLUDED
#include <fenv.h>
#define __CPROVER_FENV_H_INCLUDED
#endif

long double __sort_of_CPROVER_round_to_integrall (int rounding_mode, long double d)
{
  long double magicConst = 0x1.0p+64;
  long double return_value;
  int saved_rounding_mode = fegetround();
  fesetround(rounding_mode);
  
  if (fabsl(d) >= magicConst || d == 0.0)
  {
    return_value = d;
  }
  else
  {
    if (!signbit(d)) {
      long double tmp = d + magicConst;
      return_value = tmp - magicConst;    
    } else {
      long double tmp = d - magicConst;
      return_value = tmp + magicConst;    
    }
  }

  fesetround(saved_rounding_mode);
  return return_value;
}

/* ISO 9899:2011
 *
 * The ceil functions compute the smallest integer value not less than
 * x.
 */

/* FUNCTION: ceil */

#ifndef __CPROVER_MATH_H_INCLUDED
#include <math.h>
#define __CPROVER_MATH_H_INCLUDED
#endif

#ifndef __CPROVER_FENV_H_INCLUDED
#include <fenv.h>
#define __CPROVER_FENV_H_INCLUDED
#endif

double __sort_of_CPROVER_round_to_integral (int rounding_mode, double d);

double ceil(double x)
{
  return __sort_of_CPROVER_round_to_integral(FE_UPWARD, x);
}

/* FUNCTION: ceilf */

#ifndef __CPROVER_MATH_H_INCLUDED
#include <math.h>
#define __CPROVER_MATH_H_INCLUDED
#endif

#ifndef __CPROVER_FENV_H_INCLUDED
#include <fenv.h>
#define __CPROVER_FENV_H_INCLUDED
#endif

float __sort_of_CPROVER_round_to_integralf (int rounding_mode, float d);

float ceilf(float x)
{
  return __sort_of_CPROVER_round_to_integralf(FE_UPWARD, x);
}


/* FUNCTION: ceill */

#ifndef __CPROVER_MATH_H_INCLUDED
#include <math.h>
#define __CPROVER_MATH_H_INCLUDED
#endif

#ifndef __CPROVER_FENV_H_INCLUDED
#include <fenv.h>
#define __CPROVER_FENV_H_INCLUDED
#endif

long double __sort_of_CPROVER_round_to_integrall (int rounding_mode, long double d);

long double ceill(long double x)
{
  return __sort_of_CPROVER_round_to_integrall(FE_UPWARD, x);
}


/* ISO 9899:2011
 *
 * The floor functions compute the largest integer value not greater than x.
 */

/* FUNCTION: floor */

#ifndef __CPROVER_MATH_H_INCLUDED
#include <math.h>
#define __CPROVER_MATH_H_INCLUDED
#endif

#ifndef __CPROVER_FENV_H_INCLUDED
#include <fenv.h>
#define __CPROVER_FENV_H_INCLUDED
#endif

double __sort_of_CPROVER_round_to_integral (int rounding_mode, double d);

double floor(double x)
{
  return __sort_of_CPROVER_round_to_integral(FE_DOWNWARD, x);
}

/* FUNCTION: floorf */

#ifndef __CPROVER_MATH_H_INCLUDED
#include <math.h>
#define __CPROVER_MATH_H_INCLUDED
#endif

#ifndef __CPROVER_FENV_H_INCLUDED
#include <fenv.h>
#define __CPROVER_FENV_H_INCLUDED
#endif

float __sort_of_CPROVER_round_to_integralf (int rounding_mode, float d);

float floorf(float x)
{
  return __sort_of_CPROVER_round_to_integralf(FE_DOWNWARD, x);
}


/* FUNCTION: floorl */

#ifndef __CPROVER_MATH_H_INCLUDED
#include <math.h>
#define __CPROVER_MATH_H_INCLUDED
#endif

#ifndef __CPROVER_FENV_H_INCLUDED
#include <fenv.h>
#define __CPROVER_FENV_H_INCLUDED
#endif

long double __sort_of_CPROVER_round_to_integrall (int rounding_mode, long double d);

long double floorl(long double x)
{
  return __sort_of_CPROVER_round_to_integrall(FE_DOWNWARD, x);
}


/* ISO 9899:2011
 *
 * The trunc functions round their argument to the integer value, in
 * floating format, nearest to but no larger in magnitude than the argument.
 */

/* FUNCTION: trunc */

#ifndef __CPROVER_MATH_H_INCLUDED
#include <math.h>
#define __CPROVER_MATH_H_INCLUDED
#endif

#ifndef __CPROVER_FENV_H_INCLUDED
#include <fenv.h>
#define __CPROVER_FENV_H_INCLUDED
#endif

double __sort_of_CPROVER_round_to_integral (int rounding_mode, double d);

double trunc(double x)
{
  return __sort_of_CPROVER_round_to_integral(FE_TOWARDZERO, x);
}

/* FUNCTION: truncf */

#ifndef __CPROVER_MATH_H_INCLUDED
#include <math.h>
#define __CPROVER_MATH_H_INCLUDED
#endif

#ifndef __CPROVER_FENV_H_INCLUDED
#include <fenv.h>
#define __CPROVER_FENV_H_INCLUDED
#endif

float __sort_of_CPROVER_round_to_integralf (int rounding_mode, float d);

float truncf(float x)
{
  return __sort_of_CPROVER_round_to_integralf(FE_TOWARDZERO, x);
}


/* FUNCTION: truncl */

#ifndef __CPROVER_MATH_H_INCLUDED
#include <math.h>
#define __CPROVER_MATH_H_INCLUDED
#endif

#ifndef __CPROVER_FENV_H_INCLUDED
#include <fenv.h>
#define __CPROVER_FENV_H_INCLUDED
#endif

long double __sort_of_CPROVER_round_to_integrall (int rounding_mode, long double d);

long double truncl(long double x)
{
  return __sort_of_CPROVER_round_to_integrall(FE_TOWARDZERO, x);
}


/* ISO 9899:2011
 *
 * The round functions round their argument to the integer value, in
 * floating format, nearest to but no larger in magnitude than the argument.
 */

/* FUNCTION: round */

#ifndef __CPROVER_MATH_H_INCLUDED
#include <math.h>
#define __CPROVER_MATH_H_INCLUDED
#endif

#ifndef __CPROVER_FENV_H_INCLUDED
#include <fenv.h>
#define __CPROVER_FENV_H_INCLUDED
#endif

double __sort_of_CPROVER_round_to_integral (int rounding_mode, double d);

double round(double x)
{
  // Tempting but RNE not RNA
  // return __sort_of_CPROVER_round_to_integral(FE_TONEAREST, x);

  int saved_rounding_mode = fegetround();
  fesetround(FE_TOWARDZERO);

  double xp;
  if (x > 0.0) {
    xp = x + 0.5;
  } else if (x < 0.0) {
    xp = x - 0.5;
  } else {
    xp = x;
  }

  fesetround(saved_rounding_mode);
  
  return __sort_of_CPROVER_round_to_integral(FE_TOWARDZERO, xp);
}

/* FUNCTION: roundf */

#ifndef __CPROVER_MATH_H_INCLUDED
#include <math.h>
#define __CPROVER_MATH_H_INCLUDED
#endif

#ifndef __CPROVER_FENV_H_INCLUDED
#include <fenv.h>
#define __CPROVER_FENV_H_INCLUDED
#endif

float __sort_of_CPROVER_round_to_integralf (int rounding_mode, float d);

float roundf(float x)
{
  // Tempting but RNE not RNA
  // return __sort_of_CPROVER_round_to_integralf(FE_TONEAREST, x);

  int saved_rounding_mode = fegetround();
  fesetround(FE_TOWARDZERO);

  float xp;
  if (x > 0.0f) {
    xp = x + 0.5f;
  } else if (x < 0.0f) {
    xp = x - 0.5f;
  } else {
    xp = x;
  }

  fesetround(saved_rounding_mode);
  
  return __sort_of_CPROVER_round_to_integralf(FE_TOWARDZERO, xp);
}


/* FUNCTION: roundl */

#ifndef __CPROVER_MATH_H_INCLUDED
#include <math.h>
#define __CPROVER_MATH_H_INCLUDED
#endif

#ifndef __CPROVER_FENV_H_INCLUDED
#include <fenv.h>
#define __CPROVER_FENV_H_INCLUDED
#endif

long double __sort_of_CPROVER_round_to_integrall (int rounding_mode, long double d);

long double roundl(long double x)
{
  // Tempting but RNE not RNA
  // return __sort_of_CPROVER_round_to_integrall(FE_TONEAREST, x);

  int saved_rounding_mode = fegetround();
  fesetround(FE_TOWARDZERO);

  long double xp;
  if (x > 0.0) {
    xp = x + 0.5;
  } else if (x < 0.0) {
    xp = x - 0.5;
  } else {
    xp = x;
  }

  fesetround(saved_rounding_mode);
  
  return __sort_of_CPROVER_round_to_integrall(FE_TOWARDZERO, xp);
}



/* ISO 9899:2011
 *
 * The nearbyint functions round their argument to an integer value in
 * floating-point format, using the current rounding direction and
 * without raising the inexact floating-point exception.
 */

/* FUNCTION: nearbyint */

#ifndef __CPROVER_MATH_H_INCLUDED
#include <math.h>
#define __CPROVER_MATH_H_INCLUDED
#endif

#ifndef __CPROVER_FENV_H_INCLUDED
#include <fenv.h>
#define __CPROVER_FENV_H_INCLUDED
#endif

double __sort_of_CPROVER_round_to_integral (int rounding_mode, double d);

double nearbyint(double x)
{
  return __sort_of_CPROVER_round_to_integral(fegetround(), x);
}

/* FUNCTION: nearbyintf */

#ifndef __CPROVER_MATH_H_INCLUDED
#include <math.h>
#define __CPROVER_MATH_H_INCLUDED
#endif

#ifndef __CPROVER_FENV_H_INCLUDED
#include <fenv.h>
#define __CPROVER_FENV_H_INCLUDED
#endif

float __sort_of_CPROVER_round_to_integralf (int rounding_mode, float d);

float nearbyintf(float x)
{
  return __sort_of_CPROVER_round_to_integralf(fegetround(), x);
}


/* FUNCTION: nearbyintl */

#ifndef __CPROVER_MATH_H_INCLUDED
#include <math.h>
#define __CPROVER_MATH_H_INCLUDED
#endif

#ifndef __CPROVER_FENV_H_INCLUDED
#include <fenv.h>
#define __CPROVER_FENV_H_INCLUDED
#endif

long double __sort_of_CPROVER_round_to_integrall (int rounding_mode, long double d);

long double nearbyintl(long double x)
{
  return __sort_of_CPROVER_round_to_integrall(fegetround(), x);
}



/* ISO 9899:2011
 *
 * The rint functions differ from the nearbyint functions (7.12.9.3)
 * only in that the rint functions may raise the inexact
 * floating-point exception if the result differs in value from the argument.
 */

/* FUNCTION: rint */

#ifndef __CPROVER_MATH_H_INCLUDED
#include <math.h>
#define __CPROVER_MATH_H_INCLUDED
#endif

#ifndef __CPROVER_FENV_H_INCLUDED
#include <fenv.h>
#define __CPROVER_FENV_H_INCLUDED
#endif

double __sort_of_CPROVER_round_to_integral (int rounding_mode, double d);

double rint(double x)
{
  return __sort_of_CPROVER_round_to_integral(fegetround(), x);
}

/* FUNCTION: rintf */

#ifndef __CPROVER_MATH_H_INCLUDED
#include <math.h>
#define __CPROVER_MATH_H_INCLUDED
#endif

#ifndef __CPROVER_FENV_H_INCLUDED
#include <fenv.h>
#define __CPROVER_FENV_H_INCLUDED
#endif

float __sort_of_CPROVER_round_to_integralf (int rounding_mode, float d);

float rintf(float x)
{
  return __sort_of_CPROVER_round_to_integralf(fegetround(), x);
}

/* FUNCTION: rintl */

#ifndef __CPROVER_MATH_H_INCLUDED
#include <math.h>
#define __CPROVER_MATH_H_INCLUDED
#endif

#ifndef __CPROVER_FENV_H_INCLUDED
#include <fenv.h>
#define __CPROVER_FENV_H_INCLUDED
#endif

long double __sort_of_CPROVER_round_to_integrall (int rounding_mode, long double d);

long double rintl(long double x)
{
  return __sort_of_CPROVER_round_to_integrall(fegetround(), x);
}



/* ISO 9899:2011
 *
 * The lrint and llrint functions round their argument to the nearest
 * integer value, rounding according to the current rounding
 * direction. If the rounded value is outside the range of the return
 * type, the numeric result is unspecified and a domain error or range
 * error may occur.
 */

/* FUNCTION: lrint */

#ifndef __CPROVER_MATH_H_INCLUDED
#include <math.h>
#define __CPROVER_MATH_H_INCLUDED
#endif

#ifndef __CPROVER_FENV_H_INCLUDED
#include <fenv.h>
#define __CPROVER_FENV_H_INCLUDED
#endif

double __sort_of_CPROVER_round_to_integral (int rounding_mode, double d);

long int lrint(double x)
{
  // TODO : should be an all-in-one __CPROVER function to allow
  // conversion to SMT
  double rti = __sort_of_CPROVER_round_to_integral(fegetround(), x);
  return (long int)rti;
}

/* FUNCTION: lrintf */

#ifndef __CPROVER_MATH_H_INCLUDED
#include <math.h>
#define __CPROVER_MATH_H_INCLUDED
#endif

#ifndef __CPROVER_FENV_H_INCLUDED
#include <fenv.h>
#define __CPROVER_FENV_H_INCLUDED
#endif

float __sort_of_CPROVER_round_to_integralf (int rounding_mode, float d);

long int lrintf(float x)
{
  // TODO : should be an all-in-one __CPROVER function to allow
  // conversion to SMT
  float rti = __sort_of_CPROVER_round_to_integralf(fegetround(), x);
  return (long int)rti;
}


/* FUNCTION: lrintl */

#ifndef __CPROVER_MATH_H_INCLUDED
#include <math.h>
#define __CPROVER_MATH_H_INCLUDED
#endif

#ifndef __CPROVER_FENV_H_INCLUDED
#include <fenv.h>
#define __CPROVER_FENV_H_INCLUDED
#endif

long double __sort_of_CPROVER_round_to_integrall (int rounding_mode, long double d);

long int lrintl(long double x)
{
  // TODO : should be an all-in-one __CPROVER function to allow
  // conversion to SMT
  long double rti = __sort_of_CPROVER_round_to_integrall(fegetround(), x);
  return (long int)rti;
}


/* FUNCTION: llrint */

#ifndef __CPROVER_MATH_H_INCLUDED
#include <math.h>
#define __CPROVER_MATH_H_INCLUDED
#endif

#ifndef __CPROVER_FENV_H_INCLUDED
#include <fenv.h>
#define __CPROVER_FENV_H_INCLUDED
#endif

double __sort_of_CPROVER_round_to_integral (int rounding_mode, double d);

long long int llrint(double x)
{
  // TODO : should be an all-in-one __CPROVER function to allow
  // conversion to SMT
  double rti = __sort_of_CPROVER_round_to_integral(fegetround(), x);
  return (long long int)rti;
}

/* FUNCTION: llrintf */

#ifndef __CPROVER_MATH_H_INCLUDED
#include <math.h>
#define __CPROVER_MATH_H_INCLUDED
#endif

#ifndef __CPROVER_FENV_H_INCLUDED
#include <fenv.h>
#define __CPROVER_FENV_H_INCLUDED
#endif

float __sort_of_CPROVER_round_to_integralf (int rounding_mode, float d);

long long int llrintf(float x)
{
  // TODO : should be an all-in-one __CPROVER function to allow
  // conversion to SMT
  float rti = __sort_of_CPROVER_round_to_integralf(fegetround(), x);
  return (long long int)rti;
}


/* FUNCTION: llrintl */

#ifndef __CPROVER_MATH_H_INCLUDED
#include <math.h>
#define __CPROVER_MATH_H_INCLUDED
#endif

#ifndef __CPROVER_FENV_H_INCLUDED
#include <fenv.h>
#define __CPROVER_FENV_H_INCLUDED
#endif

long double __sort_of_CPROVER_round_to_integrall (int rounding_mode, long double d);

long long int llrintl(long double x)
{
  // TODO : should be an all-in-one __CPROVER function to allow
  // conversion to SMT
  long double rti = __sort_of_CPROVER_round_to_integrall(fegetround(), x);
  return (long long int)rti;
}


/* ISO 9899:2011
 *
 * The lround and llround functions round their argument to the
 * nearest integer value, rounding halfway cases away from zero,
 * regardless of the current rounding direction. If the rounded value
 * is outside the range of the return type, the numeric result is
 * unspecified and a domain error or range error may occur.
 */

/* FUNCTION: lround */

#ifndef __CPROVER_MATH_H_INCLUDED
#include <math.h>
#define __CPROVER_MATH_H_INCLUDED
#endif

#ifndef __CPROVER_FENV_H_INCLUDED
#include <fenv.h>
#define __CPROVER_FENV_H_INCLUDED
#endif

double __sort_of_CPROVER_round_to_integral (int rounding_mode, double d);

long int lround(double x)
{
  // TODO : should be an all-in-one __CPROVER function to allow
  // conversion to SMT, plus should use RNA

  int saved_rounding_mode = fegetround();
  fesetround(FE_TOWARDZERO);

  double xp;
  if (x > 0.0) {
    xp = x + 0.5;
  } else if (x < 0.0) {
    xp = x - 0.5;
  } else {
    xp = x;
  }

  fesetround(saved_rounding_mode);
  
  double rti = __sort_of_CPROVER_round_to_integral(FE_TOWARDZERO, xp);
  return (long int)rti;
}

/* FUNCTION: lroundf */

#ifndef __CPROVER_MATH_H_INCLUDED
#include <math.h>
#define __CPROVER_MATH_H_INCLUDED
#endif

#ifndef __CPROVER_FENV_H_INCLUDED
#include <fenv.h>
#define __CPROVER_FENV_H_INCLUDED
#endif

float __sort_of_CPROVER_round_to_integralf (int rounding_mode, float d);

long int lroundf(float x)
{
  // TODO : should be an all-in-one __CPROVER function to allow
  // conversion to SMT, plus should use RNA
  int saved_rounding_mode = fegetround();
  fesetround(FE_TOWARDZERO);

  float xp;
  if (x > 0.0f) {
    xp = x + 0.5f;
  } else if (x < 0.0f) {
    xp = x - 0.5f;
  } else {
    xp = x;
  }

  fesetround(saved_rounding_mode);
  
  float rti = __sort_of_CPROVER_round_to_integralf(FE_TOWARDZERO, xp);
  return (long int)rti;
}


/* FUNCTION: lroundl */

#ifndef __CPROVER_MATH_H_INCLUDED
#include <math.h>
#define __CPROVER_MATH_H_INCLUDED
#endif

#ifndef __CPROVER_FENV_H_INCLUDED
#include <fenv.h>
#define __CPROVER_FENV_H_INCLUDED
#endif

long double __sort_of_CPROVER_round_to_integrall (int rounding_mode, long double d);

long int lroundl(long double x)
{
  int saved_rounding_mode = fegetround();
  fesetround(FE_TOWARDZERO);

  // TODO : should be an all-in-one __CPROVER function to allow
  // conversion to SMT, plus should use RNA
  long double xp;
  if (x > 0.0) {
    xp = x + 0.5;
  } else if (x < 0.0) {
    xp = x - 0.5;
  } else {
    xp = x;
  }

  fesetround(saved_rounding_mode);
  
  long double rti = __sort_of_CPROVER_round_to_integrall(FE_TOWARDZERO, xp);
  return (long int)rti;
}


/* FUNCTION: llround */

#ifndef __CPROVER_MATH_H_INCLUDED
#include <math.h>
#define __CPROVER_MATH_H_INCLUDED
#endif

#ifndef __CPROVER_FENV_H_INCLUDED
#include <fenv.h>
#define __CPROVER_FENV_H_INCLUDED
#endif

double __sort_of_CPROVER_round_to_integral (int rounding_mode, double d);

long long int llround(double x)
{
  // TODO : should be an all-in-one __CPROVER function to allow
  // conversion to SMT, plus should use RNA
  int saved_rounding_mode = fegetround();
  fesetround(FE_TOWARDZERO);

  double xp;
  if (x > 0.0) {
    xp = x + 0.5;
  } else if (x < 0.0) {
    xp = x - 0.5;
  } else {
    xp = x;
  }

  fesetround(saved_rounding_mode);
  
  double rti = __sort_of_CPROVER_round_to_integral(FE_TOWARDZERO, xp);
  return (long long int)rti;
}

/* FUNCTION: llroundf */

#ifndef __CPROVER_MATH_H_INCLUDED
#include <math.h>
#define __CPROVER_MATH_H_INCLUDED
#endif

#ifndef __CPROVER_FENV_H_INCLUDED
#include <fenv.h>
#define __CPROVER_FENV_H_INCLUDED
#endif

float __sort_of_CPROVER_round_to_integralf (int rounding_mode, float d);

long long int llroundf(float x)
{
  // TODO : should be an all-in-one __CPROVER function to allow
  // conversion to SMT, plus should use RNA
  int saved_rounding_mode = fegetround();
  fesetround(FE_TOWARDZERO);

  float xp;
  if (x > 0.0f) {
    xp = x + 0.5f;
  } else if (x < 0.0f) {
    xp = x - 0.5f;
  } else {
    xp = x;
  }

  fesetround(saved_rounding_mode);
  
  float rti = __sort_of_CPROVER_round_to_integralf(FE_TOWARDZERO, xp);
  return (long long int)rti;
}


/* FUNCTION: llroundl */

#ifndef __CPROVER_MATH_H_INCLUDED
#include <math.h>
#define __CPROVER_MATH_H_INCLUDED
#endif

#ifndef __CPROVER_FENV_H_INCLUDED
#include <fenv.h>
#define __CPROVER_FENV_H_INCLUDED
#endif

long double __sort_of_CPROVER_round_to_integrall (int rounding_mode, long double d);

long long int llroundl(long double x)
{
  // TODO : should be an all-in-one __CPROVER function to allow
  // conversion to SMT, plus should use RNA
  int saved_rounding_mode = fegetround();
  fesetround(FE_TOWARDZERO);

  long double xp;
  if (x > 0.0) {
    xp = x + 0.5;
  } else if (x < 0.0) {
    xp = x - 0.5;
  } else {
    xp = x;
  }

  fesetround(saved_rounding_mode);
  
  long double rti = __sort_of_CPROVER_round_to_integrall(FE_TOWARDZERO, xp);
  return (long long int)rti;
}


/* ISO 9899:2011
 *
 * The modf functions break the argument value into integral and
 * fractional parts, each of which has the same type and sign as the
 * argument. They store the integral part (in floating-point format)
 * in the object pointed to by iptr.
 */

/* FUNCTION: modf */

#ifndef __CPROVER_MATH_H_INCLUDED
#include <math.h>
#define __CPROVER_MATH_H_INCLUDED
#endif

#ifndef __CPROVER_FENV_H_INCLUDED
#include <fenv.h>
#define __CPROVER_FENV_H_INCLUDED
#endif

double __sort_of_CPROVER_round_to_integral (int rounding_mode, double d);

double modf(double x, double *iptr)
{
  *iptr = __sort_of_CPROVER_round_to_integral(FE_TOWARDZERO, x);
  return (x - *iptr);
}

/* FUNCTION: modff */

#ifndef __CPROVER_MATH_H_INCLUDED
#include <math.h>
#define __CPROVER_MATH_H_INCLUDED
#endif

#ifndef __CPROVER_FENV_H_INCLUDED
#include <fenv.h>
#define __CPROVER_FENV_H_INCLUDED
#endif

float __sort_of_CPROVER_round_to_integralf (int rounding_mode, float d);

  float modff(float x, float *iptr)
{
  *iptr = __sort_of_CPROVER_round_to_integralf(FE_TOWARDZERO, x);
  return (x - *iptr);
}


/* FUNCTION: modfl */

#ifndef __CPROVER_MATH_H_INCLUDED
#include <math.h>
#define __CPROVER_MATH_H_INCLUDED
#endif

#ifndef __CPROVER_FENV_H_INCLUDED
#include <fenv.h>
#define __CPROVER_FENV_H_INCLUDED
#endif

long double __sort_of_CPROVER_round_to_integrall (int rounding_mode, long double d);

  long double modfl(long double x, long double *iptr)
{
  *iptr = __sort_of_CPROVER_round_to_integralf(FE_TOWARDZERO, x);
  return (x - *iptr);
}



/* FUNCTION: __sort_of_CPROVER_remainder */
// TODO : Should be a real __CPROVER function to convert to SMT-LIB
double __sort_of_CPROVER_round_to_integral (int rounding_mode, double d);
  
double __sort_of_CPROVER_remainder (int rounding_mode, double x, double y)
{
  if (x == 0.0 || __CPROVER_isinfd(y))
    return x;

  // Extended precision helps... a bit...
  long double div = x/y;
  long double n = __sort_of_CPROVER_round_to_integral(rounding_mode,div);
  long double res = (-y * n) + x;   // TODO : FMA would be an improvement
  return res;
}

/* FUNCTION: __sort_of_CPROVER_remainderf */
// TODO : Should be a real __CPROVER function to convert to SMT-LIB

float __sort_of_CPROVER_round_to_integralf (int rounding_mode, float d);

float __sort_of_CPROVER_remainderf (int rounding_mode, float x, float y)
{
  if (x == 0.0f || __CPROVER_isinff(y))
    return x;

  // Extended precision helps... a bit...
  long double div = x/y;
  long double n = __sort_of_CPROVER_round_to_integral(rounding_mode,div);
  long double res = (-y * n) + x;   // TODO : FMA would be an improvement
  return res;
}

/* FUNCTION: __sort_of_CPROVER_remainderl */
// TODO : Should be a real __CPROVER function to convert to SMT-LIB

long double __sort_of_CPROVER_round_to_integrall (int rounding_mode, long double d);

long double __sort_of_CPROVER_remainderl (int rounding_mode, long double x, long double y)
{
  if (x == 0.0 || __CPROVER_isinfld(y))
    return x;

  // Extended precision helps... a bit...
  long double div = x/y;
  long double n = __sort_of_CPROVER_round_to_integral(rounding_mode,div);
  long double res = (-y * n) + x;   // TODO : FMA would be an improvement
  return res;
}



/* ISO 9899:2011
 *
 * The fmod functions return the value x - ny, for some
 * integer n such that, if y is nonzero, the result has the same sign
 * as x and magnitude less than the magnitude of y. If y is zero,
 * whether a domain error occurs or the fmod functions return zero is
 * implementation-defined.
 */

/* FUNCTION: fmod */

#ifndef __CPROVER_MATH_H_INCLUDED
#include <math.h>
#define __CPROVER_MATH_H_INCLUDED
#endif

#ifndef __CPROVER_FENV_H_INCLUDED
#include <fenv.h>
#define __CPROVER_FENV_H_INCLUDED
#endif

double __sort_of_CPROVER_remainder (int rounding_mode, double x, double y);

double fmod(double x, double y) { return __sort_of_CPROVER_remainder(FE_TOWARDZERO, x, y); }


/* FUNCTION: fmodf */

#ifndef __CPROVER_MATH_H_INCLUDED
#include <math.h>
#define __CPROVER_MATH_H_INCLUDED
#endif

#ifndef __CPROVER_FENV_H_INCLUDED
#include <fenv.h>
#define __CPROVER_FENV_H_INCLUDED
#endif

float __sort_of_CPROVER_remainderf (int rounding_mode, float x, float y);

float fmodf(float x, float y) { return __sort_of_CPROVER_remainderf(FE_TOWARDZERO, x, y); }


/* FUNCTION: fmodl */

#ifndef __CPROVER_MATH_H_INCLUDED
#include <math.h>
#define __CPROVER_MATH_H_INCLUDED
#endif

#ifndef __CPROVER_FENV_H_INCLUDED
#include <fenv.h>
#define __CPROVER_FENV_H_INCLUDED
#endif

long double __sort_of_CPROVER_remainderl (int rounding_mode, long double x, long double y);

long double fmodl(long double x, long double y) { return __sort_of_CPROVER_remainderl(FE_TOWARDZERO, x, y); }



/* ISO 9899:2011
 *
 * The remainder functions compute the remainder x REM y required by
 * IEC 60559.239)
 *
 * 239) "When y != 0, the remainder r = x REM y is defined regardless
 *      of the rounding mode by the  mathematical relation r = x - n
 *      y, where n is the integer nearest the exact value of x/y;
 *      whenever | n -  x/y | = 1/2, then n is even. If r = 0, its
 *      sign shall be that of x." This definition is applicable for
 *      all implementations.
 */

/* FUNCTION: remainder */

#ifndef __CPROVER_MATH_H_INCLUDED
#include <math.h>
#define __CPROVER_MATH_H_INCLUDED
#endif

#ifndef __CPROVER_FENV_H_INCLUDED
#include <fenv.h>
#define __CPROVER_FENV_H_INCLUDED
#endif

double __sort_of_CPROVER_remainder (int rounding_mode, double x, double y);

double remainder(double x, double y) { return __sort_of_CPROVER_remainder(FE_TONEAREST, x, y); }


/* FUNCTION: remainderf */

#ifndef __CPROVER_MATH_H_INCLUDED
#include <math.h>
#define __CPROVER_MATH_H_INCLUDED
#endif

#ifndef __CPROVER_FENV_H_INCLUDED
#include <fenv.h>
#define __CPROVER_FENV_H_INCLUDED
#endif

float __sort_of_CPROVER_remainderf (int rounding_mode, float x, float y);

float remainderf(float x, float y) { return __sort_of_CPROVER_remainderf(FE_TONEAREST, x, y); }


/* FUNCTION: remainderl */

#ifndef __CPROVER_MATH_H_INCLUDED
#include <math.h>
#define __CPROVER_MATH_H_INCLUDED
#endif

#ifndef __CPROVER_FENV_H_INCLUDED
#include <fenv.h>
#define __CPROVER_FENV_H_INCLUDED
#endif

long double __sort_of_CPROVER_remainderl (int rounding_mode, long double x, long double y);

long double remainderl(long double x, long double y) { return __sort_of_CPROVER_remainderl(FE_TONEAREST, x, y); }




/* ISO 9899:2011
 * The copysign functions produce a value with the magnitude of x and
 * the sign of y. They produce a NaN (with the sign of y) if x is a
 * NaN. On implementations that represent a signed zero but do not
 * treat negative zero consistently in arithmetic operations, the
 * copysign functions regard the sign of zero as positive.
 */

/* FUNCTION: copysign */

#ifndef __CPROVER_MATH_H_INCLUDED
#include <math.h>
#define __CPROVER_MATH_H_INCLUDED
#endif

double fabs (double d);

double copysign(double x, double y)
{
  double abs = fabs(x);
  return (signbit(y)) ? -abs : abs;
}

/* FUNCTION: copysignf */

#ifndef __CPROVER_MATH_H_INCLUDED
#include <math.h>
#define __CPROVER_MATH_H_INCLUDED
#endif

float fabsf (float d);

float copysignf(float x, float y)
{
  float abs = fabs(x);
  return (signbit(y)) ? -abs : abs;
}

/* FUNCTION: copysignl */

#ifndef __CPROVER_MATH_H_INCLUDED
#include <math.h>
#define __CPROVER_MATH_H_INCLUDED
#endif

long double fabsl (long double d);

long double copysignl(long double x, long double y)
{
  long double abs = fabsl(x);
  return (signbit(y)) ? -abs : abs;
}



