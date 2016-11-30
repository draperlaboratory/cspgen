// additional test, checks void pointer use with structs and conditionals
extern void echo(int);

struct foo{
  int  a;
  _Bool b;
};

volatile struct foo bar;

void action(void* arg){
  if( ((struct foo*)arg)->b ){
    echo( (int)((struct foo*)arg)->b );
    ((struct foo*)arg)->b = !((struct foo*)arg)->b;
  }
  else {
    echo( ((struct foo*)arg)->a );
    ((struct foo*)arg)->a = ( ((struct foo*)arg)->a + 1 ) % 2;
  }
}

int main(){
  bar.a=1;
  bar.b=0;
  action((void*)&bar);
  return 0;
}
