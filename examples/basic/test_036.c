// this tests some basic void* stuff

extern void echo(int);

int is_null(void* p) {
  if(p) {
    return 0;
  } else {
    return 1;
  }
}

volatile int* q;

int main() {
  int* p;
  int x = 1;

  int result;

  // 1
  result = is_null((void*)q);  
  echo(result);

  // 0
  result = is_null((void*)&x);
  echo(result);

  // 0
  q = &x;
  result = is_null((void*)q);
  echo(result);

  // unknown
  result = is_null((void*)p);
  echo(result);

  // 0
  p = &x;
  result = is_null((void*)p);
  echo(result);

  // 1
  p = 0;
  result = is_null((void*)p);
  echo(result);

  return 0;
}
