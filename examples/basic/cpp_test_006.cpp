// This test the use of overloaded constructors in C++ classes

class Test{
    int a, b;
  public:
    Test();
    Test(int,int);
    int getSum();
};

Test::Test(){
  a = 0;
  b = 3;
}

Test::Test(int j, int k){
  a = j;
  b = k;
}

int Test::getSum(){
  return (a + b);
}

volatile int x, y;

int main(){
  Test example1;
  Test example2 (1,1);
  x = 0;
  y = 0;
  x = example1.getSum();
  y = example2.getSum();
  return 0;
}
