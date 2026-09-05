module load python3
cd /projects/standard/hsiehph/sauer354/maslov_experiment
export OMP_NUM_THREADS=4 OPENBLAS_NUM_THREADS=4
mkdir -p v6
# phase A (no dependency on the d=4 seed): d=10 and d=20 pinned p=4 runs, plus an unpinned control
nohup python3 optimize6.py pres6.json 3 seed:seed_theta_d10.json 10 2 500 20000 1 4 1 0.2 > v6/d10_p4_pin_eps0.2.log 2>&1 < /dev/null &
nohup python3 optimize6.py pres6.json 3 seed:seed_theta_d10.json 10 2 500 20000 2 4 1 0.5 > v6/d10_p4_pin_eps0.5.log 2>&1 < /dev/null &
nohup python3 optimize6.py pres6.json 3 seed:seed_theta_d10.json 10 2 500 20000 3 4 0 0.2 > v6/d10_p4_nopin_eps0.2.log 2>&1 < /dev/null &
nohup python3 optimize6.py pres6.json 3 seed:seed_theta_d10.json 10 2 500 20000 4 1 1 0.2 > v6/d10_p1_pin_eps0.2.log 2>&1 < /dev/null &
nohup python3 optimize6.py pres6.json 3 random 10 2 500 20000 6 4 1 0.2 > v6/d10_random_p4_pin.log 2>&1 < /dev/null &
echo launched A
