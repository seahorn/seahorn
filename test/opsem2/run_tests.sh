#!/usr/bin/env bash
set -euo pipefail
SEA="sea bpf --horn-bmc-engine=mono --horn-bmc --horn-bv2=true --log=opsem --horn-unify-assumes=true --horn-vcgen-only-dataflow=false --horn-bmc-coi=false "
DIR="$( cd "$( dirname "${BASH_SOURCE[0]}" )" >/dev/null 2>&1 && pwd )"

for test in $DIR/*.c;do
    $SEA $test 2>&1 | OutputCheck $test
done
