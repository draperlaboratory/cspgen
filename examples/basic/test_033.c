void echo(int);

_Bool foo () {
  return 1;
}

int main () {
  _Bool bar = foo();
  echo((int)bar);
  return 0;
}
