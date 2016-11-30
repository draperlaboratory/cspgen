// passing around global arrays as args
extern void echo(int);

volatile int x[2];

void write_arr(int *x, int n) {
  x[0] = n;
  x[1] = n+2;
  return;
}

void read_arr(int x[2]) {
  int y = x[0];
  echo(y);
  y = x[1];
  echo(y);
  return;
}

int main() {
  write_arr(x,0);
  read_arr(x);
  write_arr(x,1);
  read_arr(x);
}
