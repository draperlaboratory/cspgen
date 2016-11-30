// This tests the ternary operator.  in this particular case, the picture
// should branch because "-1" isn't represented in our model so either
// branch of the if appears possible.

void echo(int);

static int foo(int i) {
  int return_var = i>0 ? 1 : 2;
  return return_var;
}

volatile int k = 0;

int main() {
  k = foo(-1);
  k = foo(k);
  k = foo(3);
  return 0;
}
