#!/bin/bash
#SBATCH --job-name=gk3-stage2
#SBATCH --partition=msismall
#SBATCH --nodes=1 --ntasks=1 --cpus-per-task=16 --mem=48G --time=10:00:00
#SBATCH --output=/scratch.global/sauer354/gk3-strict-census-4/run_stage2.%j.log
# Binary (Q=2 by default) second and exact stages for the forward tables of shapes 3x4 and 4x3 that
# survive enum4.py, plus the 3x3 escalations as a calibration of the exact stage.
cd /scratch.global/sauer354/gk3-strict-census-4 || exit 9
echo "start=$(date -Is) host=$(hostname)"
md5sum stage2.py satcensus.py checkmodel.py enum4.py tietze.py tietze2.py oracle.py certify.py surv_3x3.jsonl surv_3x4.jsonl surv_4x3.jsonl esc_3x3_q2.jsonl
P=./venv/bin/python
Q=${Q:-2}
export DRAT_TIMEOUT=20000 CERT_MAXLENS=8,10 CERT_MAXNODES=2000000
mkdir -p proofs_lb proofs_exact
for d in 3x4 4x3; do
  ns=${d%x*}; nm=${d#*x}
  for i in 0 1 2 3 4 5 6 7; do
    SHARD=$i/8 $P stage2.py surv_$d.jsonl $ns $nm $Q st2_${d}_q${Q}_$i.jsonl esc_${d}_q${Q}_$i.jsonl proofs_lb tools/drat-trim > st2_${d}_q${Q}_$i.out 2>&1 &
  done
done
wait
echo "== stage2"; cat st2_*_q${Q}_*.out
cp esc_3x3_q2.jsonl esc_3x3_q${Q}_all.jsonl
cat esc_3x4_q${Q}_[0-7].jsonl > esc_3x4_q${Q}_all.jsonl
cat esc_4x3_q${Q}_[0-7].jsonl > esc_4x3_q${Q}_all.jsonl
wc -l esc_*_q${Q}_all.jsonl
# exact stage: realized tables by the oracle, independent certificates, SAT at realized pairs
for d in 3x3 3x4 4x3; do
  ( ns=${d%x*}; nm=${d#*x}
    $P oracle.py esc_${d}_q${Q}_all.jsonl orc_${d}_q${Q}.jsonl 1 > orc_${d}_q${Q}.out 2>&1
    $P certify.py esc_${d}_q${Q}_all.jsonl orc_${d}_q${Q}.jsonl cert_${d}_q${Q}.jsonl 7 > cert_${d}_q${Q}.out 2>&1
    $P satcensus.py strict orc_${d}_q${Q}.jsonl $ns $nm $Q exact_${d}_q${Q}.jsonl esc_${d}_q${Q}_all.jsonl proofs_exact tools/drat-trim > exact_${d}_q${Q}.out 2>&1
    $P checkmodel.py exact_${d}_q${Q}.jsonl $Q $ns $nm > check_${d}_q${Q}.out 2>&1 ) &
done
wait
for d in 3x3 3x4 4x3; do
  echo "== exact $d"
  $P - "$d" "$Q" <<'EOF'
import json, sys
d, q = sys.argv[1], sys.argv[2]
esc = [json.loads(l) for l in open(f"esc_{d}_q{q}_all.jsonl")]
orc = {r["id"]: r for r in map(json.loads, open(f"orc_{d}_q{q}.jsonl"))}
cert = {r["id"]: r for r in map(json.loads, open(f"cert_{d}_q{q}.jsonl"))}
unres = [t["id"] for t in esc if not orc[t["id"]]["resolved"]]
res = [t["id"] for t in esc if orc[t["id"]]["resolved"]]
print(json.dumps({"escalated": len(esc), "resolved": len(res), "unresolved": len(unres),
                  "unresolved_ids": unres[:30],
                  "cert_ok": sum(cert.get(i, {}).get("ok", False) for i in res),
                  "cert_missing_or_failed": [i for i in res if not cert.get(i, {}).get("ok", False)][:30],
                  "degenerate": sum(not orc[i]["labels_distinct"] for i in res)}))
EOF
  cat exact_${d}_q${Q}.out check_${d}_q${Q}.out
done
echo "end=$(date -Is) DONE"
