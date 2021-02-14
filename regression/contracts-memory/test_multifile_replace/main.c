#include <assert.h>
#include <stdbool.h>
#include "foo.h"

/*
int foo_bar() {
  int *n; 
  int o;
  ptr_ok(n);
  return_ok(o, n); 
}
*/

int main()
{
  int n = 4;
  int o = foo(&n);
  // assert(!ptr_ok(&o) && return_ok(o, &n));
  return 0;
}
