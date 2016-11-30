// for loops with break statements
extern void echo(int);

void foo(int* z) {
  int x = *z;
  int y = 0;
  for(;;) {
    echo(x);
    if(y >= 1) {break;}
    y = y + 1;
  }
  x = x + 1;
  y = 0;
  for(;;) {
    echo(x);
    if(y >= 1) {break;}
    y = y + 1;
  }
}

int main() {
  int z = 0;
  foo(&z);
  z = z + 1;
  foo(&z);
  return 0;
}
