#include <assert.h>
#include <stdbool.h>

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
{
  *x = *x + 4;
  return *x + 5;
}

