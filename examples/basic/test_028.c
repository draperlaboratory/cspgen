// This tests booleans, a bit.

typedef _Bool bool;
void echo(int);

void test(bool x) {
  if(x) {
    echo(1);
  } else {
    echo(0);
  }
}

int main() {
  bool x = 0;

  test(x);

  test(++x);

  test(++x);

  --x;

  test(x);

  return 0;

}
