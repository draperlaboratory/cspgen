
typedef struct pair {
  int y;
  int z;
} Pair;

typedef struct triple {
  int x;
  Pair p;
} Triple;

volatile Triple mytriple;
int main() {
  for (;;) {
    mytriple.x = (mytriple.x + 1)%2;
    mytriple.p.z = (mytriple.p.z + 1)%2;
  };
  return 0;
}
