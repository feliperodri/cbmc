#include <assert.h>
#include <stdbool.h>

static inline bool ptr_ok(int *x)
{
  int a;
  a = *x;
  return *x < 5;
}

static inline bool return_ok(int ret_value, int *x)
{
  int a;
  a = *x;
  return ret_value == *x + 5;
}

int foo(int *x) __CPROVER_assigns(*x) __CPROVER_requires(ptr_ok(x))
  __CPROVER_ensures(!ptr_ok(x) && return_ok(__CPROVER_return_value, x));
