// This tests reading from C++ user defined class objects

class Test{
  public:
    int a;
    Test () { a = 2; }; 
};

volatile int x;

int main(){
  x = 0;
  Test example;
  x = example.a;
  return 0;
}
