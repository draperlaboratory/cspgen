
void echo(int y);
void spawn(void (*f)());

int x = 0;

void countToTwo () {
  while(1) {
    if (x==2) break;
    x++;
  }
  echo(x);
}

void attacker () {
  x = 3;
  return;
}

int main() {
  spawn(countToTwo);
  spawn(attacker);
  return 0;
}
