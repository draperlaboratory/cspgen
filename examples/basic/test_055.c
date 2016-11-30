// test non-constant index into global array
void echo(int);

volatile int x[4] = {4,2,0,6};

int main() {
  for (int i = 0; i < 3; i++) {
    echo(x[i]);
  }
}

