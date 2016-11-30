// additional tests, checks the proper passing of integer values
extern void echo(int);

volatile int a=1; 

void rotate(){
  a=(a%3) + 1;
}

int main(){
  while(1){
    echo(a);
    rotate();
  }
  return 0;
}
