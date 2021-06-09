// Assumes a permission denominator of 2.
#define ACC_NONE 0
#define ACC_FRAC 1
#define ACC_FULL 2

// Returns true if `p` is a valid permission value.
bool is_valid_perm(int p)
{
  return (p >= ACC_NONE && p <= ACC_FULL);
}

// Returns false if `acc_1` and `acc_2` do not permit aliasing.
// Otherwise, returns `def` as the aliasing result.
bool can_alias(int acc_1, int acc_2, int def)
{
  if (acc_1 + acc_2 > ACC_FRAC)
  {
    return false;
  }
  return def;
}

// Checked if `post` permissions can be extracted from `pre` permissions.
// That is, `post` is a valid permission and `pre - post >= ACC_NONE`.
// If the check passes, then `post` is returned.
// Otherwise, the method does not return.
int borrow_permissions(int pre, int post)
{
  assume(is_valid_perm(post));
  assume(pre >= post);
  return post;
}

// Computes the permissions for a reference `x` after calling a function.
// It is assumed that:
// 1. Before calling the function, `acc(x, pre)` is true.
// 2. The function called requires `acc(x, passed)`.
// 3. The method ensures `acc(x, ret)`.
// The method returns the new permissions, i.e., `pre - passed + ret`.
int return_permissions(int pre, int passed, int ret)
{
  sassert(pre >= passed);
  sassert(passed >= ret);
  return pre - passed + ret;
}

// Computes the the value of a field `x.f` after calling a function.
// It is assumed that:
// 1. Before calling the function, `acc(x.f, pre)` is true.
// 2. Before calling the function, `x.f == v` is true.
// 3. The function requires `acc(x.f, passed)`.
// If the caller does not lose read access, then `v` is returned.
// Otherwise, a default value `def` is returned.
int update_field(int v, int pre, int passed, int def)
{
  sassert(pre >= passed);
  if (pre - passed == 0)
  {
    return def;
  }
  return v;
}
