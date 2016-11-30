// A for loop that modifies a local variable?  Insanity!

volatile int y = 0;

void foo(int start) {
  int mod4 = start % 4;
  for (;;) {
    y = mod4 % 2;
    mod4 = (mod4 + 1) % 4;
  }
  return;
}

int main() {
  foo(0);
  return 0;
}
