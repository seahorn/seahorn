// Encodes client from the viper tutorial.
// See: http://viper.ethz.ch/tutorial/?page=1&section=#non-aliasing

// Non-determinism.
extern bool client_nd1();
extern int client_nd2();
extern int client_nd3();
extern int client_nd4();
extern int client_nd5();
extern int client_nd6();
extern int client_nd7();
extern int client_nd8();
extern bool client_nd9();
extern int client_nd10();
extern int client_nd11();
extern int client_nd12();
extern int client_nd13();
extern int client_nd14();
extern int client_nd15();
extern int client_nd16();

// Invariants.
extern bool infer_client(int, int, int, int);
bool PARTIAL_FN CallerPermissions(int xf_acc_0, int yf_acc_0, int xf_acc_n, int yf_acc_n)
{
  return infer_client(xf_acc_0, yf_acc_0, xf_acc_n, yf_acc_n);
}

// Computes the permissions required by client.
// All assertions are assumed, to prune away bad function signatures.
//
// The permissions are summarized by: CallerPermissions.
void client_permissions(int af_acc, int af_val, int bf_acc, int bf_val)
{
  // inhale acc(a.f) && acc(b.f)
  af_acc = ACC_FULL;
  bf_acc = ACC_FULL;

  // Aliasing can occur if the permissions sum to at most ACC_FULL.
  bool alias_1 = can_alias(af_acc, bf_acc, client_nd1());

  // a.f := 1
  assume(af_acc == ACC_FULL);
  int af_val_1 = 1;
  int bf_val_1 = (alias_1 ? af_val_1 : bf_val);

  // b.f := 3
  assume(bf_acc == ACC_FULL);
  int bf_val_2 = 3;
  int af_val_2 = (alias_1 ? bf_val_2 : af_val_1);

  // copyAndInc(a, b)
  // * Computes the permissions passsed to copyAndInc.
  int passed_xf = borrow_permissions(af_acc, client_nd2());
  int passed_yf = borrow_permissions(bf_acc, client_nd3());
  // * Computes the permissions returned by copyAndInc.
  int returned_xf = borrow_permissions(passed_xf, client_nd4());
  int returned_yf = borrow_permissions(passed_yf, client_nd5());
  // * Assumes that the permissions are safe for the callee.
  assume(CalleePermissions(passed_xf, passed_yf, returned_xf, returned_yf));
  // * Updates the permissions of a.f and b.f according to copyAndInc.
  int af_acc_1 = return_permissions(af_acc, passed_xf, returned_xf);
  int bf_acc_1 = return_permissions(bf_acc, passed_yf, returned_yf);
  bool alias_2 = can_alias(af_acc_1, bf_acc_1, client_nd6());
  // * Assumes adversarially that the callee mutates all mutable fields.
  //   This assumption is sound, as it cannot introduce new signatures.
  //   Furthermore, this assumption can eliminate infeasible signatures.
  //   Note that infeasible signatures will necessarily fail client_safety.
  int af_rv = client_nd7();
  int bf_rv = client_nd8();
  assume(af_rv != af_val_2);
  assume(bf_rv != bf_val_2);
  // * Updates the values of a.f and b.f according to the permissions.
  int af_val_3 = update_field(af_val_2, af_acc, passed_xf, af_rv);
  int bf_val_3 = update_field(bf_val_2, bf_acc, passed_yf, bf_rv);
  if (alias_2)
  {
    assume(af_val_3 == bf_val_3);
  }
  // * Now a.f and b.f must satisfy `ensures a.f == b.f + 1`.
  assume(af_val_3 == bf_val_3 + 1);

  // assert b.f == 3 && a.f == 4
  assume(af_acc_1 >= ACC_FRAC);
  assume(bf_acc_1 >= ACC_FRAC);
  assume(bf_val_3 == 3 && af_val_3 == 4);

  // Refines permissions.
  //sassert(passed_yf == ACC_FULL);
  sassert(CallerPermissions(passed_xf, passed_yf, returned_xf, returned_yf));
}

// Assume CallerPermissions(xf_acc_0, yf_acc_0, xf_acc_n, yf_acc_n) at callsite.
// Asserts that client is safe given that copyAndInc has the signature:
//   method copyAndInc(x: Ref, y: Ref)
//     requires acc(x.f, xf_acc_0) && acc(y.f, yf_acc_0)
//     ensures acc(x.f, xf_acc_n) && acc(y.f, yf_acc_n)
//     ensures x.f = y.f + 1
void client_safety(int af_acc, int af_val, int bf_acc, int bf_val)
{
  // inhale acc(a.f) && acc(b.f)
  af_acc = ACC_FULL;
  bf_acc = ACC_FULL;

  // Aliasing can occur if the permissions sum to at most ACC_FULL.
  bool alias_1 = can_alias(af_acc, bf_acc, client_nd9());

  // a.f := 1
  sassert(af_acc == ACC_FULL);
  int af_val_1 = 1;
  int bf_val_1 = (alias_1 ? af_val_1 : bf_val);

  // b.f := 3
  sassert(bf_acc == ACC_FULL);
  int bf_val_2 = 3;
  int af_val_2 = (alias_1 ? bf_val_2 : af_val_1);

  // copyAndInc(a, b)
  // * Refers to permission summary.
  int passed_xf = client_nd10();
  int passed_yf = client_nd11();
  int returned_xf = client_nd12();
  int returned_yf = client_nd13();
  assume(CallerPermissions(passed_xf, passed_yf, returned_xf, returned_yf));
  // * Updates the permissions of a.f and b.f according to copyAndInc.
  int af_acc_1 = return_permissions(af_acc, passed_xf, returned_xf);
  int bf_acc_1 = return_permissions(bf_acc, passed_yf, returned_yf);
  bool alias_2 = can_alias(af_acc_1, bf_acc_1, client_nd14());
  // * Updates the values of a.f and b.f according to the permissions.
  int af_val_3 = update_field(af_val_2, af_acc, passed_xf, client_nd15());
  int bf_val_3 = update_field(bf_val_2, bf_acc, passed_yf, client_nd16());
  if (alias_2)
  {
    assume(af_val_3 == bf_val_3);
  }
  // * Now a.f and b.f must satisfy `ensures a.f == b.f + 1`.
  assume(af_val_3 == bf_val_3 + 1);

  // assert b.f == 3 && a.f == 4
  sassert(af_acc_1 >= ACC_FRAC);
  sassert(bf_acc_1 >= ACC_FRAC);
  sassert(bf_val_3 == 3 && af_val_3 == 4);
}
