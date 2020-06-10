#include "header.h"
#include <assert.h>

int f1(int *a, struct pair *b)
{
  struct pair_of_pairs *pop =
    (struct pair_of_pairs *)malloc(sizeof(struct pair_of_pairs));
  b = &(pop->p2);
  b->y = 5;
}

int main()
{
  int m = 4;
  struct pair n;
  f1(&m, &n);

  return 0;
}
