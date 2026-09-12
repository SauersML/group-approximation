module load python3
cd /projects/standard/hsiehph/sauer354/maslov_experiment
export OMP_NUM_THREADS=1 OPENBLAS_NUM_THREADS=1 MKL_NUM_THREADS=1
mkdir -p d4search
for s in $(seq 1 24); do
  nohup python3 optimize3.py pres6.json 2 random 4 30 600 400 $s 1.0 0.3 > d4search/m2_seed$s.log 2>&1 < /dev/null &
  nohup python3 optimize3.py pres6.json 3 random 4 30 600 400 $s 1.0 0.3 > d4search/m3_seed$s.log 2>&1 < /dev/null &
done
sleep 5
ps -u sauer354 -o pid,cmd | grep optimize3 | grep -v grep | wc -l
