// This tests ++ and --

void echo(int);

int main() {
  int x = 0;
  int y = x++;
  echo(y);
  y = ++x;
  echo(y);
  y = --x;
  echo(y);
  y = x--;
  echo(y);
  
  return 0;
}
