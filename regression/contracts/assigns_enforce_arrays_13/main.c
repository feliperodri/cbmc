#include <assert.h>

void assign_25(int a[], int len) __CPROVER_assigns(a[2, 5]);

void assign_14(int a[], int len) __CPROVER_assigns(a[1, 4]);

void assign_25(int a[], int len)
{
}

void assign_14(int a[], int len)
{
  assign_25(a, len);
}

int main()
{
  int arr[10];
  assign_14(arr, 10);

  return 0;
}
