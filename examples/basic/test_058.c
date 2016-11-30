// This checks that we push stack values in the right order.

typedef struct {
  int x;
  void (**f)();
} S;

void echo(int);

void inspect(S* s) {
  echo(s->x);
}

int main() {
  S s;
  inspect(&s);
  return 0;
}
