// This tests recursive structs
struct int_list {
  int val;
  struct int_list *next;
};

volatile struct int_list x,y;

extern void echo(int x);

void echo_list(struct int_list *l) {
  if(l) {
    echo(l -> val);
    echo_list(l -> next);
  } else {
    return;
  }
}

int main () {
  x.val  = 1;
  x.next = &y;
  y.val  = 2;
  struct int_list z;
  y.next = &z;
  z.val  = 3;
  z.next = 0;
  echo_list(&x);
  return 0;
}
