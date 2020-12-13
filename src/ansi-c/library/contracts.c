
/* FUNCTION: __CPROVER_is_fresh */
#pragma GCC diagnostic ignored "-Wunused-parameter"
_Bool __CPROVER_is_fresh(const void *ptr, __CPROVER_size_t size, unsigned flags) {
    __CPROVER_assert(0, "__CPROVER_is_fresh called outside of contract function.");
    return 0;
}

/* FUNCTION: is_fresh */
#pragma GCC diagnostic ignored "-Wunused-parameter"
_Bool is_fresh(const void *ptr, __CPROVER_size_t size, unsigned flags) {
    flags = flags + 1;
    return 1;
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