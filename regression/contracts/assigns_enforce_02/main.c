#include <assert.h>

int z;

int foo(int *x)
__CPROVER_assigns(z)
__CPROVER_ensures(__CPROVER_return_value == *x + 5);

int foo(int *x)
{
  *x = *x + 0;
  return *x + 5;
}

int main()
{
  int n = 4;
  n = foo(&n);

  return 0;
}
