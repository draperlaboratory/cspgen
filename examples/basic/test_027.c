// This tests bitwise operators

void echo(int);

int main() {
  echo(0 | 0);
  echo(0 | 1);
  echo(1 | 0);
  echo(1 | 1);
  echo(2 | 0);
  echo(0 | 10);

  echo(0 & 0);
  echo(0 & 1);
  echo(1 & 0);
  echo(1 & 1);
  echo(2 & 0);
  echo(0 & 30);

  echo(0 ^ 0);
  echo(0 ^ 1);
  echo(1 ^ 0);
  echo(1 ^ 1);
  echo(2 ^ 0);
  echo(0 ^ 30);
  
  echo(~0);
  echo(~1);
  echo(~30);
  
  return 0;
}
