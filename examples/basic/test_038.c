// this tests pthread_create

#include <pthread.h>

extern void echo(int);

volatile int ft_set = 0;
volatile pthread_t first_thread;
volatile pthread_t second_thread;

void* check (void* ft) {
  while(!ft_set) {
  }

  pthread_t me = pthread_self();
  if (pthread_equal(me,*(pthread_t*)ft)) {
    echo(0);
  } else {
    echo(1);
  }
}

int main() {
  pthread_create(&first_thread,NULL,check,(void*) &first_thread);
  ft_set = 1;
  pthread_create(&second_thread,NULL,check,(void*) &first_thread);
  return 0;
}
