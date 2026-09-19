#!/bin/sh
# Reproduce experiments/fpbs-shield-exponent-2026-09-18/results.txt.
# Run from this directory. It is single-threaded; each production run is
# wrapped in `nice -n 10 timeout 1200`.
#   (1) validation: the linear-time pinch-wall evaluator phi_fast.c against
#       the block (Tarjan) evaluator theta_chain.c of
#       experiments/fpbs-finger-shield-exponent-2026-09-18, sample by sample
#       (the two programs share the configuration generator);
#   (2) production: stream A (N=1024, 40 x 400 samples, seeds 1001..1040) and
#       stream B (N=2048, 60 x 100 samples, seeds 2001..2060), nested boxes
#       n = 8,16,...,N of one configuration;
#   (3) pooling with 20-block jackknife errors (pool.py).
# Streams can be cut short: pool.py only uses files that finished.
set -e
TC=../fpbs-finger-shield-exponent-2026-09-18/theta_chain.c
cc -O2 -o phi_fast phi_fast.c -lm
# patch theta_chain.c to print the per-sample outcome of the pattern-free event
sed '197s/cntb\[b\]\[c\]+=ok;/& if(c==0) fprintf(stderr,"S %ld %d\\n",s,ok);/' $TC > tc_dbg.c
cc -O2 -o tc_dbg tc_dbg.c -lm
echo "# validation: phi_fast vs theta_chain, per sample, 1500 samples per n"
for n in 4 8 16 32; do
  ./phi_fast $n 1500 7 0.5 $n 1 | grep '^S' | awk '{print $2, $3%2}' > pf_$n.txt
  ./tc_dbg $n 1500 7 2>&1 >/dev/null | grep '^S' | awk '{print $2, $3}' > tc_$n.txt
  echo "n=$n mismatches=$(diff pf_$n.txt tc_$n.txt | grep -c '^<' || true)"
done
mkdir -p runs
for sd in $(seq 1001 1040); do
  nice -n 10 timeout 1200 ./phi_fast 1024 400 $sd 0.5 8 1 > runs/A_$sd.txt || true
done
for sd in $(seq 2001 2060); do
  nice -n 10 timeout 1200 ./phi_fast 2048 100 $sd 0.5 8 1 > runs/B_$sd.txt || true
done
python3 pool.py 'runs/A_*.txt' 'runs/B_*.txt' 'runs/*.txt'
