// additional test, checks pointer use and if statements
extern void echo(int);

void action(int* a,int* b){
  //
  if(*a){
    echo(*a);
    *a = (*a + 1)%2;
  }
  else if(*b){
    echo(*b);
    *b= (*b + 1)%2;
  }
}

int main(){
  int x,y=1;
  action(&x,&y);
  return 0;
}