#include <assert.h>

void assign_25(int a[], int len) __CPROVER_assigns(a[2, 5]);

void assign_37(int a[], int len) __CPROVER_assigns(a[3, 7]);

void assign_25(int a[], int len)
{
}

void assign_37(int a[], int len)
{
  assign_25(a, len);
}

int main()
{
  int arr[10];
  assign_37(arr, 10);

  return 0;
}
