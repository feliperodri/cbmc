#include <assert.h>
#include <stdbool.h>
// #include <cprover.h>
double fabs(double a);
_Bool __CPROVER_is_fresh(const void *mem, __CPROVER_size_t size, unsigned flags);
_Bool is_fresh(const void *mem, __CPROVER_size_t size, unsigned flags);
void bzero(void *s, __CPROVER_size_t n);

int z;

bool ptr_ok(int *x) {
	int a;
	a = *x; 
	return *x < 5;
}

bool return_ok(int ret_value, int *x) {
	int a; 
	a = *x;
	return ret_value == *x + 5; 
}

int foo(int *x) 
__CPROVER_assigns(z, *x)
__CPROVER_requires(ptr_ok(x))
__CPROVER_ensures(!ptr_ok(x) && *x < 1000 && return_ok(__CPROVER_return_value, x));

int foo(int *x)
{
  *x = *x + 4;
  return *x + 5;
}

int main()
{
  int n = 4;
  int o = foo(&n);
  int p = n;
  int q = o;
  float r = -1.0;
  bzero(&q, sizeof(int));
  assert(q == 0);
  assert(fabs(r) == r);
  assert(!ptr_ok(&o) && return_ok(o, &n));
  assert(is_fresh(&n, sizeof(int), 0));
  assert(__CPROVER_is_fresh(&n, sizeof(int), 0));
  return 0;
}
