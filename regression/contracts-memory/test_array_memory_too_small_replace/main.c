#include <assert.h>
#include <stdbool.h>
#include <stddef.h>
#include <stdint.h>
#include <stdlib.h>

bool dummy_fn(int *n)
{
  assert(__CPROVER_is_fresh(&n, sizeof(int)));
  int *x = malloc(sizeof(int));
}

bool ptr_ok(int *x)
{
  return *x < 5;
}

bool return_ok(int ret_value, int *x)
{
  int a;
  a = *x;
  return ret_value == *x + 5;
}

// The 'ensures' __CPROVER_is_fresh test is unnecessary, but left in just to test the function is working correctly.
// If you remove the negation, the program will fail, because 'x' is not fresh.

int foo(int *x, int y) __CPROVER_assigns(*x) __CPROVER_requires(
  __CPROVER_is_fresh(x, sizeof(int) * 10) && x[0] > 0 && ptr_ok(x))
  __CPROVER_ensures(
    !ptr_ok(x) && !__CPROVER_is_fresh(x, sizeof(int) * 10) && x[9] == 113 &&
    return_ok(__CPROVER_return_value, x));

int foo(int *x)
{
  *x = *x + 4;
  x[5] = 12;
  x[9] = 113;
  int y = *x + 5;
  return *x + 5;
}

int main()
{
  int *n = malloc(sizeof(int) * 9);
  n[0] = 3;
  int o = foo(n);
  assert(o >= 10 && o == *n + 5);
  return 0;
}