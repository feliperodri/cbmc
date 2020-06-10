#include <assert.h>

void f1(int a[], int len) __CPROVER_assigns(a[2, 5]);

void f1(int a[], int len)
{
  int *indr;
  indr = a + 3;
  *indr = 5;
}

int main()
{
  int arr[10];
  f1(arr, 10);

  return 0;
}
