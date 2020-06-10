#include <assert.h>

int idx = 4;

int nextIdx() __CPROVER_assigns(idx);

void f1(int a[], int len) __CPROVER_assigns(idx, a[2, 5]);

int nextIdx()
{
  idx++;
  return idx;
}

void f1(int a[], int len)
{
  a[nextIdx()] = 5;
}

int main()
{
  int arr[10];
  f1(arr, 10);

  assert(idx == 5);

  return 0;
}
