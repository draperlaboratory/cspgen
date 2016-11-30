void echo(int y);
void spawn(void (*f)());

int x = 0;

void addOne() {
  int y = ++x;
  echo(y);
}

int main() {
  spawn(addOne);
  spawn(addOne);
  return 0;
}
