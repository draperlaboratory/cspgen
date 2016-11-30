// floats!
extern void echo(int);

int main () {
  float x = 0.3;
  for (; x < 0.9; ) {
    x = x + 0.1;
    echo(0);
  }  
  echo(1);
  return 0;
}
