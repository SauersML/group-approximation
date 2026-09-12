module load python3
cd /projects/standard/hsiehph/sauer354/maslov_experiment
pkill -u sauer354 -f optimize2.py; sleep 1
export OMP_NUM_THREADS=4 OPENBLAS_NUM_THREADS=4 MKL_NUM_THREADS=4
run() { nohup python3 optimize3.py pres6.json "$@" > "o3_m$1_$2_d$3.log" 2>&1 < /dev/null & }
run 3 trivial 4 4 800 600 1 1.0 0.3
run 3 trivial 8 4 800 600 1 1.0 0.3
run 3 trivial 16 3 800 400 1 1.0 0.3
run 3 perm2 16 3 800 400 1 1.0 0.3
run 2 trivial 4 4 800 600 1 1.0 0.3
run 2 trivial 8 4 800 600 1 1.0 0.3
run 2 trivial 16 3 800 400 1 1.0 0.3
run 2 perm2 16 3 800 400 1 1.0 0.3
run 3 random 8 4 800 600 1 1.0 0.3
sleep 40
ps -u sauer354 -o pid,etime,cmd | grep optimize3 | grep -v grep | wc -l
for f in o3_*.log; do echo "== $f"; tail -n 2 "$f"; done
