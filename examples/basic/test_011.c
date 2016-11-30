// This tests if statements.  in this particular case, the picture
// should branch because "-1" isn't represented in our model so either
// branch of the if appears possible.

static int foo(int i) {
  int return_var;
  if (i > 0) 
    {return_var = 1;}
  else 
    {return_var = 2;}
  return return_var;
}

volatile int k = 0;

int main() {
  int z;
  k = foo(z);
  k = foo(k);
  k = foo(3);
  return 0;
}
