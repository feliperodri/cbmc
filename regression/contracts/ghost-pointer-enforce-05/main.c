void foo(int *x, int *y) __CPROVER_assigns(*x, *y)
  __CPROVER_ensures(*x == *x_ + 2 || *y == *y_ + 3)
{
  *x = *x + 1;
  *y = *y + 2;
}

int main()
{
  int x, y;
  foo(&x, &y);

  return 0;
}
