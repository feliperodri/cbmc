#include <assert.h>

void foo(int *x) __CPROVER_assigns(*x) __CPROVER_requires(*x == 0)
  __CPROVER_ensures(*x > *x_ + 2)
{
  *x = *x + 2;
}

int main()
{
  int x = 0;
  foo(&x);

  assert(x > 2);
  assert(!(x <= 2));

  return 0;
}
