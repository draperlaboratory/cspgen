// this tests the ability of a thread to get its pid and to compare pids.

#include <pthread.h>

extern void echo(int);
extern void spawn(void (*f)());

volatile pthread_t first_thread;

volatile int ft_set = 0;

void check () {
  while(!ft_set) {
  }

  pthread_t me = pthread_self();
  if (pthread_equal(me,first_thread)) {
    echo(0);
  } else {
    echo(1);
  }
}

void set_and_check () {
  first_thread = pthread_self();
  ft_set = 1;
  check();
}

int main() {
  spawn(set_and_check);
  spawn(check);
  return 0;
}
