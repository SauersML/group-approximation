#!/bin/bash
#SBATCH --job-name=gk-census4
#SBATCH --partition=msismall
#SBATCH --nodes=1 --ntasks=1 --cpus-per-task=8 --mem=32G --time=4:00:00
#SBATCH --output=/scratch.global/sauer354/hl-gottschalk-dynamics/run4.%j.log
cd /scratch.global/sauer354/hl-gottschalk-dynamics || exit 9
echo "start=$(date -Is) host=$(hostname)"
md5sum oracle.py certify.py tietze.py tietze2.py census.py census2.py enum_tables.py
PY=/usr/bin/python3.12
# 1. exact Tietze decisions (cyclic, free, free abelian of rank two), cross-checked with the oracle
for d in 2x2 2x3 3x2 3x3; do $PY tietze2.py tables_$d.jsonl tietze2_$d.jsonl oracle_$d.jsonl; done
# 2. oracle v3: unresolved tables replaced by their exact Tietze decision
$PY - <<'EOF'
import json
for d in ["2x2", "2x3", "3x2", "3x3"]:
    tz = {r["id"]: r for r in map(json.loads, open(f"tietze2_{d}.jsonl"))}
    fixed = still = 0
    with open(f"oracle_{d}_v3.jsonl", "w") as fh:
        for o in map(json.loads, open(f"oracle_{d}.jsonl")):
            if not o["resolved"]:
                dd = tz[o["id"]]
                if dd["kind"] != "undecided":
                    o = dd; fixed += 1
                else:
                    still += 1
            fh.write(json.dumps(o) + "\n")
    print("v3", d, "tietze_fixed", fixed, "still_unresolved", still)
# certification set: tables Tietze does not decide exactly
    undec = [json.loads(l) for l in open(f"tables_{d}.jsonl") if tz[json.loads(l)["id"]]["kind"] == "undecided"]
    lines = [json.dumps(t) for t in undec]
    k = 8 if d == "3x3" else 1
    for i in range(k):
        open(f"certset_{d}_{i}.jsonl", "w").write("\n".join(lines[i::k]) + ("\n" if lines[i::k] else ""))
    print("certset", d, len(undec))
EOF
# 3. certificates for the undecided tables, oracle proven parameters first
export CERT_MAXLENS=8,10 CERT_MAXNODES=2000000
for d in 2x2 2x3 3x2; do $PY certify.py certset_${d}_0.jsonl oracle_${d}_v3.jsonl cert4_${d}_0.jsonl 7 > cert4_${d}.out 2>&1 & done
wait
for i in 0 1 2 3 4 5 6 7; do $PY certify.py certset_3x3_$i.jsonl oracle_3x3_v3.jsonl cert4_3x3_$i.jsonl 7 > cert4_3x3_$i.out 2>&1 & done
wait
# 4. censuses on v3, both implementations
for d in 2x2 2x3 3x2 3x3; do ./venv/bin/python census.py tables_$d.jsonl oracle_${d}_v3.jsonl 2 census4_q2_$d.json > census4_q2_$d.out 2>&1 & done
for d in 2x2 2x3 3x2 3x3; do $PY census2.py tables_$d.jsonl oracle_${d}_v3.jsonl 2 > census4b_q2_$d.out 2>&1 & done
wait
echo "== certificates over Tietze-undecided tables"; cat cert4_*.out
cat cert4_*.jsonl | $PY -c "import sys,json; r=[json.loads(l) for l in sys.stdin if l.strip()]; print('certified', sum(x['ok'] for x in r), 'failed', sum(not x['ok'] for x in r), 'failed_ids', [x['id'] for x in r if not x['ok']])"
echo "== census.py"; cat census4_q2_*.out
echo "== census2.py"; cat census4b_q2_*.out
echo "end=$(date -Is) DONE"
