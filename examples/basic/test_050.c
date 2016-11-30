// test some stuff with local, statically-allocated arrays.
extern void echo(int);

int main() {
  int x[3];

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
