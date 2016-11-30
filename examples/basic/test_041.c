// additional tests, checks for proper passing and conversion of void pointers
extern void echo(int);

volatile int a = 1;

void action(void* arg){
  echo(*(int*)arg);
}

int main(){
  while(1){
    action((void*)&a);
    a = (a+1)%2;
  }
  return 0;
}
