struct pair
{
  int x;
  int y;
};

struct pair_of_pairs
{
  struct pair p1;
  struct pair p2;
};

int f1(int *a, struct pair *b) __CPROVER_assigns(*a);
