// This tests the use of C++ classes and objects

class Test{
    int a, b;
  public:
    void setter(int,int);
    int  getSum();
};

void Test::setter(int x, int y){
  a = x;
  b = y;
}

int Test::getSum(){
  return (a + b);
}

volatile int x;

int main(){
  Test example;
  x = 0;
  example.setter(1,1);
  x = example.getSum();
  return 0;
}
