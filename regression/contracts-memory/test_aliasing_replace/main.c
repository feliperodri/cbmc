/* is_unique_02_enforce: designed to demonstrate that aliasing will be caught by the is_fresh predicate 
   Enforce will work, but replace will fail (expectedly) */

#include <assert.h>
#include <stdbool.h>

int z;

void bar(int argument); 

/* dummy_for_definitions(int *n) {
  assert(__CPROVER_is_fresh(&n, sizeof(int)));
  int *x = malloc(sizeof(int));
}
*/

int foo(int *x, int *y)
__CPROVER_assigns(z, *x, *y)
__CPROVER_requires(__CPROVER_is_fresh(x, sizeof(int)) &&
                   __CPROVER_is_fresh(y, sizeof(int)) && *x > 0 && *x < 4)
__CPROVER_ensures(__CPROVER_return_value == *x + 5); 

int foo(int *x, int *y)
{
  //bar(4);
  *x = *x + 4;
  return *x + 5;
}

int main()
{
  int n = 4;
  n = foo(&n, &n);
  assert(!(n < 4));
  return 0;
}
