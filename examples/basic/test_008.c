
typedef struct {
  int x;
  int y;
} pair;

volatile int k;

volatile pair mypair;

void incr(pair* p) {
  p -> x = ((p -> x) + 1) % 2;
  p -> y = ((p -> y) + 1) % 2;
  return;
}

int main() {
  for (;;) {
    incr(&mypair);
  };
  return 0;
}
