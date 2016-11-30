// test out-of-bounds error
extern void echo(int);

volatile int x[3];

int main() {
  x[0] = 1;
  x[1] = 2;
  x[2] = 3;

  echo(x[0]);
  echo(x[1]);
  echo(x[2]);

  x[3] = 4;

  return 0;
}
