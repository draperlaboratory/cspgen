// test simple array initialization and use

extern void echo(int);

volatile int count, buf[3];

void actionOne(){  
  buf[0] = 1;
  count++;
}

void actionTwo(){  
  buf[1] = 2;
  count++;
}

void actionThree(){  
  buf[2] = 3;
  count++;
}

int main(){
  actionOne();
  actionTwo();
  actionThree();
  echo(buf[0]);
  echo(buf[1]);
  echo(buf[2]);
  return 0;
}
