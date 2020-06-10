#include <assert.h>

void assign_17(int a[], int len) __CPROVER_assigns(a[1, 7]);

void assign_25(int a[], int len) __CPROVER_assigns(a[2, 5]);

void assign_17(int a[], int len)
{
}

void assign_25(int a[], int len)
{
  assign_17(a, len);
}

int main()
{
  int arr[10];
  assign_25(arr, 10);

  return 0;
}
