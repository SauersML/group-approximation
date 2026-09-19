module load python3
cd /projects/standard/hsiehph/sauer354/maslov_experiment
export OMP_NUM_THREADS=4 OPENBLAS_NUM_THREADS=4
python3 make_abmin_seeds.py
mkdir -p v7
# args: pres modulus init d restarts iters n_unl seed beta pin eps0 [stages]
nohup python3 optimize7.py pres6.json 3 seed:seed_theta_d4_abmin.json 4 3 400 20000 41 30 0 0.05 > v7/d4_b30_eps0.05.log 2>&1 < /dev/null &
nohup python3 optimize7.py pres6.json 3 seed:seed_theta_d4_abmin.json 4 3 400 20000 42 30 0 0.3 > v7/d4_b30_eps0.3.log 2>&1 < /dev/null &
nohup python3 optimize7.py pres6.json 3 seed:seed_theta_d4_abmin.json 4 3 400 20000 43 100 0 0.05 > v7/d4_b100_eps0.05.log 2>&1 < /dev/null &
nohup python3 optimize7.py pres6.json 3 seed:seed_theta_4p4_d8_abmin.json 8 2 400 20000 44 30 0 0.1 > v7/d8_b30_eps0.1.log 2>&1 < /dev/null &
nohup python3 optimize7.py pres6.json 3 seed:seed_theta_d10_abmin.json 10 2 400 15000 45 30 0 0.05 > v7/d10_b30_eps0.05.log 2>&1 < /dev/null &
nohup python3 optimize7.py pres6.json 3 seed:seed_theta_d10_abmin.json 10 2 400 15000 46 30 0 0.3 > v7/d10_b30_eps0.3.log 2>&1 < /dev/null &
nohup python3 optimize7.py pres6.json 3 seed:seed_theta_4x3_d12_abmin.json 12 2 400 15000 47 30 0 0.1 > v7/d12_b30_eps0.1.log 2>&1 < /dev/null &
nohup python3 optimize7.py pres6.json 3 seed:seed_theta_10p4_d14_abmin.json 14 2 400 12000 48 30 0 0.1 > v7/d14_b30_eps0.1.log 2>&1 < /dev/null &
nohup python3 optimize7.py pres6.json 3 seed:seed_theta_10p10_d20_abmin.json 20 1 300 6000 49 30 0 0.1 > v7/d20_b30_eps0.1.log 2>&1 < /dev/null &
nohup python3 optimize7.py pres6.json 3 random 4 3 400 20000 50 30 0 0.2 > v7/d4_random_b30.log 2>&1 < /dev/null &
nohup python3 optimize7.py pres6.json 3 seed:seed_theta_d4_abmin.json 4 2 400 20000 51 30 1 0.3 > v7/d4_b30_pin_eps0.3.log 2>&1 < /dev/null &
sleep 2; echo launched v7: $(ps -u sauer354 -o cmd | grep -c "^python3 optimize7")
