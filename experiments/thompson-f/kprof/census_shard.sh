#!/bin/bash
# Census shard: all pairs a < b of nonzero elements of F_2[S_(3,5)] with a % NSH == SH, degree by degree
# k = 0..KMAX with window N = k+3. At each k only pairs with zero kernel so far are tested.
# Writes census/sh${SH}/first.txt lines "a b first_degree kernel_at_first" and survivors_k.txt.
set -u
SH=$1; NSH=$2; KMAX=$3
cd /scratch.global/sauer354/hl-f-kernel-profiles
W=census/sh$SH; mkdir -p $W
/usr/bin/python3.12 -c "
for a in range(1, 512):
    if a % $NSH != $SH: continue
    for b in range(a + 1, 512):
        print(a, b)" > $W/pairs_0.txt
: > $W/first.txt
for k in $(seq 0 $KMAX); do
  t0=$(date +%s)
  ./kprof S35 $k 3 ore - < $W/pairs_$k.txt > $W/out_$k.jsonl
  rc=$?
  nin=$(wc -l < $W/pairs_$k.txt); nout=$(wc -l < $W/out_$k.jsonl)
  if [ "$rc" -ne 0 ] || [ "$nin" -ne "$nout" ]; then echo "ABORT k=$k rc=$rc in=$nin out=$nout"; exit 3; fi
  /usr/bin/python3.12 - $W $k <<'EOF'
import json, sys
W, k = sys.argv[1], int(sys.argv[2])
surv = []
with open(f"{W}/first.txt", "a") as ff:
    for line in open(f"{W}/out_{k}.jsonl"):
        d = json.loads(line)
        if d["kernel"] > 0:
            ff.write(f"{d['a']} {d['b']} {k} {d['kernel']}\n")
        else:
            surv.append((d["a"], d["b"]))
open(f"{W}/pairs_{k+1}.txt", "w").write("".join(f"{a} {b}\n" for a, b in surv))
print("K", k, "tested", sum(1 for _ in open(f"{W}/pairs_{k}.txt")), "survivors", len(surv), flush=True)
EOF
  echo "k=$k rc=$rc secs=$(( $(date +%s) - t0 ))"
  n=$(wc -l < $W/pairs_$((k+1)).txt)
  [ "$n" -eq 0 ] && break
done
echo SHARD_DONE
