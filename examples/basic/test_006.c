
typedef struct {
  int *foo;
  char bar;
  char *baz;
} chan_c;

volatile int y = 0;
volatile chan_c z;


void incr(int* x) {
  *x = (*x + 1) % 2;
  return;
}


int main() {
  for (;;) {
    incr(&y);
  };
  return 0;
}
