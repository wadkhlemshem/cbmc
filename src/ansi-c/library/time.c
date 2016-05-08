/* FUNCTION: time */

#ifndef __CPROVER_TIME_H_INCLUDED
#include <time.h>
#define __CPROVER_TIME_H_INCLUDED
#endif

#undef time

inline time_t time(time_t *tloc)
{
  __CPROVER_HIDE:;
  time_t res;
  if(!tloc) *tloc=res;
  return res;
}

/* FUNCTION: gmtime */

#ifndef __CPROVER_TIME_H_INCLUDED
#include <time.h>
#define __CPROVER_TIME_H_INCLUDED
#endif

#undef gmtime

inline struct tm *gmtime(const time_t *clock)
{
  __CPROVER_HIDE:;
  // not very general, may be too restrictive
  // need to set the fields to something meaningful
  (void)*clock;
  #ifdef __CPROVER_CUSTOM_BITVECTOR_ANALYSIS
  __CPROVER_event("invalidate_pointer", "gmtime_result");
  struct tm *gmtime_result;
  __CPROVER_set_may(gmtime_result, "gmtime_result");
  return gmtime_result;
  #else
  static struct tm return_value;
  return &return_value;
  #endif
}

/* FUNCTION: gmtime_r */

#ifndef __CPROVER_TIME_H_INCLUDED
#include <time.h>
#define __CPROVER_TIME_H_INCLUDED
#endif

#undef gmtime

inline struct tm *gmtime_r(const time_t *clock, struct tm *result)
{
  __CPROVER_HIDE:;
  // need to set the fields to something meaningful
  (void)*clock;
  return result;
}

/* FUNCTION: localtime */

#ifndef __CPROVER_TIME_H_INCLUDED
#include <time.h>
#define __CPROVER_TIME_H_INCLUDED
#endif

#undef localtime

inline struct tm *localtime(const time_t *clock)
{
  __CPROVER_HIDE:;
  // not very general, may be too restrictive
  // need to set the fields to something meaningful
  (void)*clock;
  #ifdef __CPROVER_CUSTOM_BITVECTOR_ANALYSIS
  __CPROVER_event("invalidate_pointer", "localtime_result");
  struct tm *localtime_result;
  __CPROVER_set_may(localtime_result, "localtime_result");
  return localtime_result;
  #else
  static struct tm return_value;
  return &return_value;
  #endif
}

/* FUNCTION: localtime_r */

#ifndef __CPROVER_TIME_H_INCLUDED
#include <time.h>
#define __CPROVER_TIME_H_INCLUDED
#endif

#undef localtime

inline struct tm *localtime_r(const time_t *clock, struct tm *result)
{
  __CPROVER_HIDE:;
  // need to set the fields to something meaningful
  (void)*clock;
  return result;
}

/* FUNCTION: mktime */

#ifndef __CPROVER_TIME_H_INCLUDED
#include <time.h>
#define __CPROVER_TIME_H_INCLUDED
#endif

#undef mktime

inline time_t mktime(struct tm *timeptr)
{
  __CPROVER_HIDE:;
  (void)*timeptr;
  time_t result;
  return result;
}

/* FUNCTION: timegm */

#ifndef __CPROVER_TIME_H_INCLUDED
#include <time.h>
#define __CPROVER_TIME_H_INCLUDED
#endif

#undef timegm

inline time_t timegm(struct tm *timeptr)
{
  __CPROVER_HIDE:;
  (void)*timeptr;
  time_t result;
  return result;
}

/* FUNCTION: asctime */

#ifndef __CPROVER_TIME_H_INCLUDED
#include <time.h>
#define __CPROVER_TIME_H_INCLUDED
#endif

inline char *asctime(const struct tm *timeptr)
{
  __CPROVER_HIDE:;
  (void)*timeptr;
  #ifdef __CPROVER_CUSTOM_BITVECTOR_ANALYSIS
  __CPROVER_event("invalidate_pointer", "asctime_result");
  char *asctime_result;
  __CPROVER_set_may(asctime_result, "asctime_result");
  return asctime_result;
  #endif
}

/* FUNCTION: ctime */

#ifndef __CPROVER_TIME_H_INCLUDED
#include <time.h>
#define __CPROVER_TIME_H_INCLUDED
#endif

inline char *ctime(const time_t *clock)
{
  __CPROVER_HIDE:;
  (void)*clock;
  #ifdef __CPROVER_CUSTOM_BITVECTOR_ANALYSIS
  __CPROVER_event("invalidate_pointer", "ctime_result");
  char *ctime_result;
  __CPROVER_set_may(ctime_result, "ctime_result");
  return ctime_result;
  #endif
}

