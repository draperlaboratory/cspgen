// test out-of-bounds error on local array
extern void echo(int);

int main() {
  int x[3];

  x[0] = 1;
  x[1] = 2;
  x[2] = 3;

  echo(x[0]);
  echo(x[1]);
  echo(x[2]);

  x[3] = 4;

  return 0;
}
