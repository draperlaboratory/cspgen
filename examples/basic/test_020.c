// nested loops
extern void echo(int);

int main() {
  do {
    for(int x = 0; x < 3; x = x + 1) {
      echo(x);
    }
  } while (1);
  return 0;
}
