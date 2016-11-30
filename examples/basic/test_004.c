volatile int y = 0;

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
