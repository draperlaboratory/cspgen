// This one tests nested if statements, which was the source of a bug previously.

static int foo(int i) {
  int return_var;
  if (i > 0) {return_var = 1;}
  else {
    if (i < 0) {return_var = (-1);}
    else {
      return_var = 0;
    }
  }
  return return_var;
}

volatile int y = 0;

int main() {
  y = foo(3);
  y = foo(y);
  y = foo(-1);
  return 0;
}
