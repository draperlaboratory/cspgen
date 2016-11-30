// passing around the addresses of local variables
extern void echo(int);

void foo(int* x) {
  echo(*x);
  *x = 2;
  echo(*x);
  *x = *x + 1;
  echo(*x - 2);
}

int main() {
  int x;
  foo(&x);
  return 0;
}
