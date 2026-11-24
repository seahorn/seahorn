// sea yama: -y NAME that is not a file is looked up as NAME.yaml in
// $SEAHORN_PROFILE_PATH (then <prefix>/share/seahorn/profiles). Options
// before the first word (--bound=8) are dropped as on dev18, unless a -y
// named a profile or --ylead-opts is given.
// RUN: rm -rf %t.d
// RUN: mkdir -p %t.d
// RUN: printf 'verify_options:\n  command: bpf\n  horn-bmc-engine: sea-mlir\n' > %t.d/myprof.yaml
// RUN: env SEAHORN_PROFILE_PATH=%t.d %sea yama -y myprof --dry-run --bound=8 %s | filecheck %s --check-prefix=NAME
// RUN: %sea yama -y %t.d/myprof.yaml --dry-run --bound=8 %s | filecheck %s --check-prefix=FILE
// RUN: %sea yama -y %t.d/myprof.yaml --ylead-opts --dry-run --bound=8 %s | filecheck %s --check-prefix=LEAD
// NAME: Yama using profile myprof: {{.*}}myprof.yaml
// NAME: bpf --horn-bmc-engine=sea-mlir --bound=8 {{.*}}yama_profile.c
// FILE: bpf --horn-bmc-engine=sea-mlir /{{[^ ]*}}yama_profile.c
// LEAD: bpf --horn-bmc-engine=sea-mlir --bound=8 {{.*}}yama_profile.c

int main(void) { return 0; }
