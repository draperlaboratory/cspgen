// this tests casts

void echo(int);

int main () {
  _Bool foo = 0;
  int bar = foo;
  echo(bar);
  echo((int)foo);
  echo(foo ? 0 : 1);
  return 0;
}
