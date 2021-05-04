#include <assert.h>
#include <stddef.h>

void bar(int *x, int *y) __CPROVER_assigns(*x, *y) __CPROVER_requires(*x > 0)
  __CPROVER_ensures(*x == 3 && (y == NULL || *y == 5))
{
  *x = 3;
  if(y != NULL)
    *y = 5;
}

void foo(int *x) __CPROVER_assigns(*x) __CPROVER_requires(*x > 0)
  __CPROVER_ensures(*x == 3)
{
  bar(x, NULL);
  *x = 3;
}

int main()
{
  int n;
  foo(&n);

  assert(n == 3);
  return 0;
}
