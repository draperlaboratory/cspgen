// additional test, checks void pointer use with if statements
extern void echo(int);

volatile int x,y=1;

void action(void* a,void* b){
  //
  if(*(int*)a){
    echo(*(int*)a);
    *(int*)a = (*(int*)a + 1)%2;
  }
  else if(*(int*)b){
    echo(*(int*)b);
    *(int*)b= (*(int*)b + 1)%2;
  }
}

int main(){
  action((void*)&x,(void*)&y);
  return 0;
}
