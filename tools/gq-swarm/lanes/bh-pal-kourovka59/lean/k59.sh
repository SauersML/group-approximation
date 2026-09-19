#!/bin/bash
# Lane scratch compiler: private oleans under $R/build, never the shared .lake.
set -u
export PATH=$HOME/.elan/bin:$PATH
R=/projects/standard/hsiehph/sauer354/k1759
cd /projects/standard/hsiehph/sauer354/nonsofic_existence || exit 1
mkdir -p $R/build/GroupApproximation/Kourovka1759
for m in "$@"; do
  echo "== $m"
  LEAN_NUM_THREADS=4 timeout 1500 lake env bash -c "export LEAN_PATH=$R/build:\$LEAN_PATH; lean --root=$R/src -o $R/build/GroupApproximation/Kourovka1759/$m.olean $R/src/GroupApproximation/Kourovka1759/$m.lean" > $R/log-$m.txt 2>&1
  st=$?
  grep -v '^warning: ' $R/log-$m.txt | head -c 30000
  echo "== $m exit $st"
  [ $st -eq 0 ] || break
done
echo K59_SENTINEL
