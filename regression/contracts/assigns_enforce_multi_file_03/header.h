void assigns_single(int a[], int len) __CPROVER_assigns(a[8]);

void assigns_upper_bound(int a[], int len) __CPROVER_assigns(a[2, 5]);

void assigns_lower_bound(int a[], int len) __CPROVER_assigns(a[2, 5]);
