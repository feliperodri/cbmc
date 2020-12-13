#include <assert.h>
#include <stdbool.h>


bool ptr_ok(int *x) ;
bool return_ok(int ret_value, int *x);

int foo(int *x) 
__CPROVER_assigns(*x)
__CPROVER_requires(ptr_ok(x))
__CPROVER_ensures(!ptr_ok(x) && *x < 1000 && return_ok(__CPROVER_return_value, x));

