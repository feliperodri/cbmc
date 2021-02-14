#include <stdlib.h>
//#include "cprover.h"


/* FUNCTION: __CPROVER_is_fresh */
#pragma GCC diagnostic ignored "-Wunused-parameter"
_Bool __CPROVER_is_fresh(const void *ptr, __CPROVER_size_t size) {
    __CPROVER_assert(0, "__CPROVER_is_fresh called outside of contract function.");
    return 0;
}

// 
// Below are templates of the functions that 
// will be instantiated for each contract function.
// 

extern _Bool __CPROVER_FUN_NAME_memory_map[]; 

/* FUNCTION: __CPROVER_FUN_NAME_requires_is_fresh */
_Bool __CPROVER_FUN_NAME_requires_is_fresh(void **elem, __CPROVER_size_t size) {
	*elem = malloc(size);
	if (!*elem || __CPROVER_FUN_NAME_memory_map[(unsigned long)*elem]) return 0;

	__CPROVER_FUN_NAME_memory_map[(unsigned long)*elem] = 1;
	return 1;
}

/* FUNCTION: __CPROVER_FUN_NAME_ensures_is_fresh */
_Bool __CPROVER_FUN_NAME_ensures_is_fresh(void *elem, __CPROVER_size_t size) {
	_Bool ok = (!__CPROVER_FUN_NAME_memory_map[(unsigned long)elem] && __CPROVER_r_ok(elem, size));
	__CPROVER_FUN_NAME_memory_map[(unsigned long)elem] = 1;
	return ok;
}

/* FUNCTION: __CPROVER_FUN_NAME_call_requires_is_fresh */
_Bool __CPROVER_FUN_NAME_call_requires_is_fresh(void *elem, __CPROVER_size_t size) {
	_Bool r_ok = __CPROVER_r_ok(elem, size);
	if (__CPROVER_FUN_NAME_memory_map[(unsigned long)elem] || !r_ok)  return 0;
	__CPROVER_FUN_NAME_memory_map[(unsigned long)elem] = 1;
	return 1;
}

/* FUNCTION: __CPROVER_FUN_NAME_call_ensures_is_fresh */
_Bool __CPROVER_FUN_NAME_call_ensures_is_fresh(void **elem, __CPROVER_size_t size) {
	*elem = malloc(size);
	return (*elem != NULL);
}

/*
inline _Bool __CPROVER_is_fresh_assume(const void **ptr, __CPROVER_size_t size, unsigned flags) {
  void *conc = NULL; 
  conc = malloc(size);
  bool nondet = nondet_bool();
  if (!conc || nondet) { 
      return false; 
  }
  *ptr = conc;
  return true; 
}
*/