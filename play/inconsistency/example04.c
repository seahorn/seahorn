

int main() {

  int x = 5;

  int a_size = 1;
  int a[a_size];
  a[0] = 1;
  //binary_search(a, a_size, x);
  int first = 0;
  int last = a_size;

  while (first < last) {
    // Midpoint
    int m = (first + last) / 2;

    if (a[m] == x) {
      // Found it
      return m;
    } else if (a[m] < x) {
      // It's bigger than midpoint, go [m+1, last)
      first = m;
    } else {
      // It's smaller then midpoint, go [first, m)
      last = m;
    }
  }
}
