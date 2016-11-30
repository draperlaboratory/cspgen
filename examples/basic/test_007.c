
typedef struct pair {
  int x;
  int y;
} MyPair;

volatile MyPair mypair;
volatile int k = 0;

void assignk(struct pair* p) {
  p -> x = k;
  p -> y = k;
  return;
}

int main() {
  for (;;) {
    assignk(&mypair);
    k = (k + 1) % 2;
  };
  return 0;
}
