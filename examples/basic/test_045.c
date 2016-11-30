// test some stuff with global, statically-allocated arrays.
extern void echo(int);

volatile int x[3];

int main() {
  echo(x[0]);
  echo(x[1]);
  echo(x[2]);

  x[1] = 3;
  echo(x[0]);
  echo(x[1]);
  echo(x[2]);

  x[0] = 2;
  x[2] = 1;
  echo(x[0]);
  echo(x[1]);
  echo(x[2]);

  x[1] = x[0] + x[2] - 1;
  echo(x[0]);
  echo(x[1]);
  echo(x[2]);
  
  x[2] = x[1] + x[2];
  echo(x[0]);
  echo(x[1]);
  echo(x[2]);

  return 0;
}
