extern void echo(int);

int main() {
  for(int x = 0; x < 3; x = x + 1) {
    echo(x);
  }
  return 0;
}
