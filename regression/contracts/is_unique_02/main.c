#include <assert.h>
#include <stdbool.h>

int z;


int foo(int *x, int y)
__CPROVER_assigns(z, *x)
__CPROVER_requires(*x < 4)
__CPROVER_ensures(__CPROVER_return_value == *x + 5); 

int foo(int *x, int y)
{
  *x = *x + 4;
  return *x + 5;
}

int main()
{
  int n = 4;
  n = foo(&n, 3);

  return 0;
}
