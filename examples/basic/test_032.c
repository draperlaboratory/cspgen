void echo(int);

// test array assignment.
int main () {
  int foo[30];
  foo[3] = 0;
  int x = foo[3];
  echo(x);
  echo(foo[3]);
  x = foo[4];
  echo(x);
  echo(foo[4]);
  return 0;
}
