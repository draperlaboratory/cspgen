// this tests mutex functionality

#include <pthread.h>

extern void echo(int);

volatile pthread_t firstThread;
volatile pthread_t secondThread;
volatile pthread_mutex_t lock;
volatile int count, start;

void* firstAction(void* arg){
  while(1){
    if(!start){
      pthread_mutex_lock(&lock);
      start = 1;
      count = (++count) % 4;
      echo(count);
      pthread_mutex_unlock(&lock);
    }
  }
  return NULL;
}

void* secondAction(void* arg){
  while(1){
    if(start){
      pthread_mutex_lock(&lock);
      start = 0;
      count = (count+3) % 4;
      echo(count);
      pthread_mutex_unlock(&lock);
    }
  }
  return NULL;
}

int main(){
  if(pthread_mutex_init(&lock,NULL) != 0){
    return 1;
  }
  pthread_create(&firstThread, NULL, firstAction, NULL);
  pthread_create(&secondThread, NULL, secondAction, NULL);
  return 0;
}
