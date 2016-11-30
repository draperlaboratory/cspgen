// floats!
extern void echo(int);

volatile float x;

int main () {
  for (x = 0.0; x < 0.9; ) {
    x = x + 0.1;
    echo(0);
  }  
  echo(1);
  return 0;
}
