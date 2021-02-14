#include <assert.h>
#include <stdbool.h>
#include "foo.h"

/*
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
*/

int main()
{
  int n = 4;
  int o = foo(&n);

  return 0;
}
