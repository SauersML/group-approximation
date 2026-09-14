#!/bin/bash
#SBATCH --job-name=gk3-q3census
#SBATCH --partition=msismall
#SBATCH --nodes=1 --ntasks=1 --cpus-per-task=16 --mem=64G --time=12:00:00
#SBATCH --output=/scratch.global/sauer354/gk3-strict-census-4/run_q3.%j.log
# Ternary census of strict rectangle data at every closed 3x3 table (realized reverse tables from
# the certified oracle of the binary census). Encoding A with DRUP proofs checked by drat-trim,
# encoding B (independent code, CaDiCaL) as the second implementation.
cd /scratch.global/sauer354/gk3-strict-census-4 || exit 9
echo "start=$(date -Is) host=$(hostname)"
md5sum satcensus.py satcensus2.py checkmodel.py enum_tables.py oracle_3x3_v3.jsonl tables_3x3.jsonl tools/drat-trim.c
P=./venv/bin/python
mkdir -p proofs_q2 proofs_q3
export DRAT_TIMEOUT=20000
# calibration of the proof path: the binary census again, every UNSAT proof checked by drat-trim
$P satcensus.py strict oracle_3x3_v3.jsonl 3 3 2 q2A_proofs.jsonl tables_3x3.jsonl proofs_q2 tools/drat-trim
for i in 0 1 2 3 4 5 6 7; do
  SHARD=$i/8 $P satcensus.py strict oracle_3x3_v3.jsonl 3 3 3 q3A_$i.jsonl tables_3x3.jsonl proofs_q3 tools/drat-trim > q3A_$i.out 2>&1 &
  SHARD=$i/8 $P satcensus2.py oracle_3x3_v3.jsonl 3 3 3 q3B_$i.jsonl tables_3x3.jsonl > q3B_$i.out 2>&1 &
done
wait
echo "== encoding A"; cat q3A_*.out
echo "== encoding B"; cat q3B_*.out
cat q3A_*.jsonl > q3A_all.jsonl; cat q3B_*.jsonl > q3B_all.jsonl
$P checkmodel.py q3A_all.jsonl 3 3 3
$P checkmodel.py q3B_all.jsonl 3 3 3
$P - <<'EOF'
import json
a = {tuple(sorted(r["ids"])): r for r in map(json.loads, open("q3A_all.jsonl"))}
b = {tuple(sorted(r["ids"])): r for r in map(json.loads, open("q3B_all.jsonl"))}
print(json.dumps({"pairs_A": len(a), "pairs_B": len(b), "same_pairs": set(a) == set(b),
                  "sat_A": sum(r["sat"] for r in a.values()), "sat_B": sum(r["sat"] for r in b.values()),
                  "disagree": [k for k in a if k in b and a[k]["sat"] != b[k]["sat"]][:10],
                  "drat_verified": sum(r.get("drat") == "VERIFIED" for r in a.values()),
                  "unsat_A": sum(not r["sat"] for r in a.values())}))
EOF
du -sh proofs_q3
echo "end=$(date -Is) DONE"
