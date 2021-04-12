void foo(int *x, int *y) __CPROVER_assigns(*x, *y)
  __CPROVER_ensures(*x == *y_ + 1 && *y == *x_ + 2)
{
  int x_initial = *x;
  *x = *y + 1;
  *y = x_initial + 2;
}

int main()
{
  int x, y;
  foo(&x, &y);

  return 0;
}
