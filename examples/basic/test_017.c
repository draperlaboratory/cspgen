// nested loops with breaks
extern void echo(int);

void foo(int* z) {
  int x = *z;
  for(;;) {
    int z;
    z = 0;
    for(;;) {
      echo(x);
      if(z >= 1) {break;}
      z = z + 1;
    }
    if (x >= 1) {break;}
    x = x + 1;
  }
}

int main() {
  int z = 0;
  foo(&z);
  return 0;
}
