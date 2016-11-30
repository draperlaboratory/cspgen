// This test the use of constructors in C++ classes

class Test{
    int a, b;
  public:
    Test(int,int);
    int  getSum();
};

Test::Test(int j, int k){
  a = j;
  b = k;
}

int Test::getSum(){
  return (a + b);
}

volatile int x;

int main(){
  x = 0;
  Test example (1,1);
  x = example.getSum();
  return 0;
}
