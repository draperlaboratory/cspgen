// this test generates GEP instructions with non-zero first indices, in the llvm
// version.

void echo(int);

void readArr(int *x) {
  echo(x[0]);
  echo(x[1]);
  echo(x[2]);
}

volatile int a[3] = {2,1,2};

int main() {
  int b[3];
  b[0] = 1;
  b[1] = 3;
  b[2] = 1;
  readArr(a);
  readArr(b);
  return 0;
}


