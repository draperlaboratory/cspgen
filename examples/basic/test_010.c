// This tests repeated updates to a local variable.

volatile int y = 0;

int update(int* loc) {
  int k = 1;
  k = k + 1;
  k = k + 1;
  *loc = k;
  return (k + 1);
}

int main() {
  y = update(&y);
  return 0;
}
