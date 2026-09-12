module load python3
cd /projects/standard/hsiehph/sauer354/maslov_experiment
pkill -u sauer354 -f optimize4.py; sleep 2
export OMP_NUM_THREADS=1 OPENBLAS_NUM_THREADS=1 MKL_NUM_THREADS=1
rm -f spinsearch/spin_seed*.log spinsearch/basin_eps*.log
python3 optimize4.py pres6.json file:spin_phases.json seed:seed_spin_d4.json 4 1 5 400 0 1.0 0.0 > spinsearch/seed_check2.log 2>&1
tail -n 1 spinsearch/seed_check2.log
for s in $(seq 1 24); do
  nohup python3 optimize4.py pres6.json file:spin_phases.json random 4 30 600 400 $s 1.0 0.3 > spinsearch/spin_seed$s.log 2>&1 < /dev/null &
done
for e in 0.3 0.6 1.0 1.5 2.5; do
  nohup python3 optimize4.py pres6.json file:spin_phases.json seed:seed_spin_d4.json 4 6 600 400 7 1.0 $e > spinsearch/basin_eps$e.log 2>&1 < /dev/null &
done
sleep 3; ps -u sauer354 -o pid,cmd | grep optimize4 | grep -v grep | wc -l
