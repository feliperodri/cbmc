#include <assert.h>

void assign_out_under(int a[], int len) 
__CPROVER_assigns(a[2,5]);

void assign_out_under(int a[], int len) 
{
 a[1] = 5;
}

int main()
{
  int arr[10];
  assign_out_under(arr, 10);

  return 0;
}
