volatile int y = 0;

void incr() {
  y = (y + 1) % 2;
  incr();
}


int main() {
  incr();
  return 0;
}
