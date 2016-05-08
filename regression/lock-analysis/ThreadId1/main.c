#include <pthread.h>

void *thread(void *arg)
{
  return 0;
}

int main()
{
  pthread_t tid;
  pthread_create(&tid, 0, thread, 0);

  int x;
  x = 743;

  pthread_join(tid, 0);

  x = 853;  

  return 0;
}

