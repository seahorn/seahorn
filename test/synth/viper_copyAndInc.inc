// Encodes copyAndInc from the viper tutorial.
// See: http://viper.ethz.ch/tutorial/?page=1&section=#non-aliasing

// Non-determinism.
extern bool copyAndInc_nd1();
extern int copyAndInc_nd2();
extern int copyAndInc_nd3();
extern int copyAndInc_nd4();
extern int copyAndInc_nd5();
extern bool copyAndInc_nd6();

// Invariants.
extern bool infer_copyAndInc(int, int, int, int);
bool PARTIAL_FN CalleePermissions(int xf_acc_0, int yf_acc_0, int xf_acc_n, int yf_acc_n)
{
  return infer_copyAndInc(xf_acc_0, yf_acc_0, xf_acc_n, yf_acc_n);
}

// Computes the permissions required by copyAndInc.
// All assertions are assumed, to prune away bad inputs.
//
// The permissions are summarized by: CalleePermissions.
void copyAndInc_Permissions(int xf_acc, int xf_val, int yf_acc, int yf_val)
{
  // Aliasing can occur if the permissions sum to at most ACC_FULL.
  bool alias = can_alias(xf_acc, yf_acc, copyAndInc_nd1());

  // x.f := y.f + 1
  assume(xf_acc == ACC_FULL);
  assume(yf_acc >= ACC_FRAC);
  int xf_val_1 = yf_val + 1;
  int yf_val_1 = (alias ? xf_val_1 : yf_val);

  // ensures x.f == y.f + 1
  assume(xf_val_1 == yf_val_1 + 1);

  // Returns some amount of the remaining permissions.
  int xf_acc_n = copyAndInc_nd2();
  int yf_acc_n = copyAndInc_nd3();
  assume(xf_acc_n >= 0);
  assume(xf_acc_n <= xf_acc);
  assume(yf_acc_n >= 0);
  assume(yf_acc_n <= yf_acc);
  sassert(CalleePermissions(xf_acc, yf_acc, xf_acc_n, yf_acc_n));
}

// Assume any CalleePermissions(xf_acc_0, yf_acc_0, xf_acc_n, yf_acc_n).
// Asserts that the following signature is verifiable:
//   method copyAndInc(x: Ref, y: Ref)
//     requires acc(x.f, xf_acc_0) && acc(y.f, yf_acc_0)
//     ensures acc(x.f, xf_acc_n) && acc(y.f, yf_acc_n)
//     ensures x.f = y.f + 1
void copyAndInc_safety(int xf_acc, int xf_val, int yf_acc, int yf_val)
{
  // Assumes summary.
  int xf_acc_n = copyAndInc_nd4();
  int yf_acc_n = copyAndInc_nd5();
  assume(CalleePermissions(xf_acc, yf_acc, xf_acc_n, yf_acc_n));

  // Aliasing can occur if the permissions sum to at most ACC_FULL.
  bool alias = can_alias(xf_acc, yf_acc, copyAndInc_nd6());

  // x.f := y.f + 1
  sassert(xf_acc == ACC_FULL);
  sassert(yf_acc >= ACC_FRAC);
  int xf_val_1 = yf_val + 1;
  int yf_val_1 = (alias ? xf_val_1 : yf_val);

  // ensures x.f == y.f + 1
  sassert(xf_val_1 == yf_val_1 + 1);

  // Asserts that the ensured permissions are feasible.
  sassert(xf_acc_n >= 0);
  sassert(xf_acc_n <= xf_acc);
  sassert(yf_acc_n >= 0);
  sassert(yf_acc_n <= yf_acc);
}
