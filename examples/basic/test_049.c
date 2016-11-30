// additional test for mutex functionality

#include <pthread.h>

extern void echo(int);

volatile pthread_t first_thread;
volatile pthread_t second_thread;
volatile pthread_mutex_t lock;
volatile int count, start;

void* action(void* arg){
  pthread_t self = pthread_self();
  if(pthread_equal(self,first_thread))
    while(!start);
  int i, j;

  pthread_mutex_lock(&lock);
  start = 1;
  count = 0;
  echo(count);

  count = (++count) % 4;
  echo(count);
  pthread_mutex_unlock(&lock);
  return NULL;
}

int main(){
  if(pthread_mutex_init(&lock,NULL) != 0){
    return 1;
  }
  pthread_create(&first_thread, NULL, action, NULL);
  pthread_create(&second_thread, NULL, action, NULL);
  return 0;
}
