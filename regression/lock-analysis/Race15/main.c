#include <pthread.h>

int x;

void * thr (void * arg)
{
  ++x;                       // expect: 1586
  return 0;
}

int main (void)
{
	pthread_t tid1, tid2;
  pthread_create(&tid1, 0, &thr, 0);
  pthread_create(&tid2, 0, &thr, 0);

  pthread_join(tid1, 0);
  pthread_join(tid2, 0);

  return x;
}
