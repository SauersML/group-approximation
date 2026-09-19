#!/bin/sh
# Reproduction of the length-23 three-level (n = 3) certificates, from a checkout of the repo root.
# Each step: nice -n 10, single-threaded, ulimit -v 2000000.  K = kbmag bin directory.
X=experiments/one-relator-length23-three-level-2026-09-18
L21=experiments/one-relator-length21-singular-hierarchy-2026-09-18
TM=experiments/one-relator-top-magnus-intersection-2026-09-18
export PYTHONPATH=research/artifacts/or-unpeelable-census-scripts-2026-09-12
ulimit -v 2000000
# 0. census: n = 1, 2, 3 give 2226, 8041, 96 candidates, n = 4, 5, 6 give none (w23n*.err).
# cert23.py resets the certificate budget for each relator.
for n in 1 2 3 4 5 6; do nice -n 10 python3 $L21/gen_walk21.py 23 $n > /tmp/w23n$n.seq 2> /tmp/w23n$n.err; done
nice -n 10 python3 $X/cert23.py $X/w23n3.seq > $X/w23n3.cert                    # 96 OPEN
for n in 1 2; do nice -n 10 python3 $X/cert23.py /tmp/w23n$n.seq > $X/w23n$n.cert; done   # 0 and 7961 OPEN
awk '{print $2}' $X/w23n3.cert > /tmp/rel96.txt
# 1. top-level sZ in the original presentation (16 finite) and rebased y = t a (the other 80)
nice -n 10 python3 $L21/topsz.py /tmp/rel96.txt > $X/top96.out
grep -e '-> None' $X/top96.out | awk '{print $2}' > /tmp/fail80.txt
python3 $X/rebase.py /tmp/fail80.txt 1 R > $X/rebased80.txt
awk '{print $1}' $X/rebased80.txt > /tmp/rb80.txt
nice -n 10 python3 $L21/topsz.py /tmp/rb80.txt > $X/top_rebased80.out
# 2. level one, both presentations
nice -n 10 python3 $TM/level1.py /tmp/rel96.txt > $X/l1_96.out
nice -n 10 python3 $TM/level1.py /tmp/rb80.txt > $X/l1_rebased80.out
# 3. hyperbolicity: default autgroup (120 s), then autgroup -large (240 s) on the 29 failures
nice -n 10 sh $X/kbhyp2.sh $K /tmp/rel96.txt 120 > $X/kb96.out
grep AUTGROUP-FAIL $X/kb96.out | awk '{print $2}' > /tmp/kbfail29.txt
AUTOPT=-large nice -n 10 sh $X/kbhyp2.sh $K /tmp/kbfail29.txt 240 > $X/kb29large.out
# 4. per-relator verdict
python3 $X/merge23.py > $X/verdict23.out                                       # certified 96 of 96
