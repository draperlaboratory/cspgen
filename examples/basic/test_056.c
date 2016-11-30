// test non-constant index into local array
void echo(int);

int main() {
  int x[4];
  x[0] = 4;
  x[1] = 2;
  x[2] = 0;
  x[3] = 6;
  for (int i = 0; i < 3; i++) {
    echo(x[i]);
  }
}

