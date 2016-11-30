volatile int y = 0;

void incr() {
  while(1) {
    y = (y + 1) % 2;
  };
  return;
}


int main() {
  incr();
  return 0;
}
