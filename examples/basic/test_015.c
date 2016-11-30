// passing around the addresses of local variables
extern void echo(int);

void foo(int* x, int *y) {
  int z = 1;
  int* z_addr = &z;
  if(*y) {*z_addr = 0;};
  for(;;) {
    echo(*x);
    *x = (*x + *z_addr) % 2;
  }
}

int main() {
  int x,y;
  x = 0;
  foo(&x,&y);
  return 0;
}
