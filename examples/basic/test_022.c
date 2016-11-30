// nested loops with breaks
extern void echo(int);

int main() {
  for (int x = 0; 1; x = (x + 1)%2) {
    int y = 0;
    while (y < 2) {
      y = y + 1;
      int z = 0;
      do {
        z = z + 1;
        if (z >= 3) {break;};
        echo (x+z);
      } while (1);
    }
  }
  return 0;
}
