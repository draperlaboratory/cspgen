// This tests the shift operations

void echo(int x);

int main() {
  echo(0 << 2);
  echo(0 << 30);
  echo(1 << 1);
  echo(2 << 0);
  echo(8 << 1);

  echo(0 >> 0);
  echo(0 >> 3);
  echo(2 >> 1);

  return 0;
}
