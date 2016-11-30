// This tests that our reachability analysis helps prevent our liveness analysis
// from cleaning up variables prematurely.
//
// In particular, the old, non-reachabilty aware liveness analysis would "clean
// up" the variable "x" after the line:
//
//    int* z = &x;
//
// which appears to be the last use of x.  But the reachability analysis can see
// that x remains reachable from z, and thus it does not get cleaned up any
// more.

void echo(int x);

int main () {
  int x = 1;
  echo(x);
  int* z = &x;
  echo(*z);
  return 0;
}
