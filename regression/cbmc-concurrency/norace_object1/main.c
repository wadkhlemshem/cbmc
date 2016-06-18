#include <pthread.h>
#include <assert.h>
#include <stdlib.h>

struct mystruct { int f0; int f1; };

struct mystruct *s;

void* thread_0(void* arg)
{
  s->f0 = 2;
  assert(s->f0 == 2);
  return NULL;
}

void* thread_1(void* arg)
{
  s->f1 = 1;
  assert(s->f1 == 1);
  return NULL;
}

int main(void)
{
  s = malloc(sizeof(struct mystruct));
  pthread_t thread0, thread1;
  pthread_create(&thread0, NULL, thread_0, 0);
  pthread_create(&thread1, NULL, thread_1, 0);
  return 0;
}
