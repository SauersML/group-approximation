#!/bin/bash
#SBATCH --job-name=nm-khsearch
#SBATCH --partition=msismall
#SBATCH --cpus-per-task=16
#SBATCH --mem=96G
#SBATCH --time=02:00:00
#SBATCH --output=/projects/standard/hsiehph/sauer354/nm/khsearch/job-%j.out
#
# One bounded search job (lane kh-hyperbolic, lead-approved 2026-09-11):
# a sigma-invariant W(8) triangle table, sigma a free element of order ORDER
# (65 = q^2+1, the Singer-type torus, by default; 13 for the approved follow-up).
#   1. w8model.py: W(8) in the Lean coordinates and the free element;
#   2. w8encode.py: the exact-cover CNF;
#   3. CaDiCaL (built once from source under tools/), NRUN runs with distinct
#      seeds, the first to finish decides (all runs share one formula, so SAT or
#      UNSAT from any run is the answer);
#   4. w8decode.py verifies a model from scratch and writes table.json.
# Submit as:  sbatch --export=ALL,ORDER=13 run_search.sbatch
set -u
ORDER=${ORDER:-65}
K=/projects/standard/hsiehph/sauer354/nm/khsearch
PY=/projects/standard/hsiehph/sauer354/params-venv/bin/python3
W=$K/o$ORDER
mkdir -p "$W"
cp "$K"/src/w8model.py "$K"/src/w8encode.py "$K"/src/w8decode.py "$W"/ || exit 2
cd "$W" || exit 2
if [ "$ORDER" -ge 65 ]; then NRUN=15; TMO=6600; else NRUN=8; TMO=5400; fi
date
$PY w8model.py 8 "$ORDER" 1 model.json || exit 3
/usr/bin/time -v $PY w8encode.py model.json w8.cnf w8.map.json 2> encode.time || { cat encode.time; exit 4; }
grep -E 'Maximum resident|Elapsed' encode.time
head -1 w8.cnf
date
if [ ! -x "$K"/tools/cadical/build/cadical ]; then
  mkdir -p "$K"/tools && cd "$K"/tools
  [ -d cadical ] || git clone -q https://github.com/arminbiere/cadical.git
  cd cadical && ./configure > configure.log 2>&1 && make -j 8 > make.log 2>&1 || { tail -20 make.log; exit 5; }
  cd "$W"
fi
CAD="$K"/tools/cadical/build/cadical
$CAD --version
pids=()
for s in $(seq 1 $NRUN); do
  timeout $TMO $CAD --seed=$s -q w8.cnf > run-$s.out 2>&1 &
  pids+=($!)
done
winner=""
while [ -z "$winner" ]; do
  if ! wait -n; then :; fi
  for s in $(seq 1 $NRUN); do
    if grep -qE '^s (SATISFIABLE|UNSATISFIABLE)' run-$s.out 2>/dev/null; then winner=$s; break; fi
  done
  alive=0
  for p in "${pids[@]}"; do kill -0 "$p" 2>/dev/null && alive=1; done
  [ $alive -eq 0 ] && break
done
for p in "${pids[@]}"; do kill "$p" 2>/dev/null; done
date
if [ -z "$winner" ]; then echo "SEARCH RESULT: UNKNOWN (order $ORDER, timeout, no run decided)"; rm -f w8.cnf; exit 0; fi
grep '^s ' run-$winner.out
if grep -q '^s SATISFIABLE' run-$winner.out; then
  $PY w8decode.py model.json w8.map.json run-$winner.out table.json && echo "SEARCH RESULT: TABLE FOUND (order $ORDER, run $winner)"
else
  echo "SEARCH RESULT: UNSATISFIABLE (order $ORDER, run $winner): no W(8) triangle table is invariant under a free element of order $ORDER"
fi
rm -f w8.cnf
