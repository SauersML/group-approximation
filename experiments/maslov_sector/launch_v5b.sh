module load python3
cd /projects/standard/hsiehph/sauer354/maslov_experiment
export OMP_NUM_THREADS=4 OPENBLAS_NUM_THREADS=4
python3 make_sum_seeds.py
mkdir -p v5
nohup python3 optimize5.py pres6.json 3 seed:seed_theta_d4.json 4 3 500 20000 11 4 1 0.2 > v5/d4_p4_pin_eps0.2.log 2>&1 < /dev/null &
nohup python3 optimize5.py pres6.json 3 seed:seed_theta_d4.json 4 3 500 20000 12 4 1 0.5 > v5/d4_p4_pin_eps0.5.log 2>&1 < /dev/null &
nohup python3 optimize5.py pres6.json 3 seed:seed_theta_4p4_d8.json 8 2 500 20000 13 4 1 0.2 > v5/d8_p4_pin_eps0.2.log 2>&1 < /dev/null &
nohup python3 optimize5.py pres6.json 3 seed:seed_theta_4x3_d12.json 12 2 500 20000 14 4 1 0.2 > v5/d12_p4_pin_eps0.2.log 2>&1 < /dev/null &
nohup python3 optimize5.py pres6.json 3 seed:seed_theta_10p4_d14.json 14 2 500 20000 15 4 1 0.2 > v5/d14_p4_pin_eps0.2.log 2>&1 < /dev/null &
nohup python3 optimize5.py pres6.json 3 seed:seed_theta_10p10_d20.json 20 1 400 20000 16 4 1 0.2 > v5/d20sum_p4_pin_eps0.2.log 2>&1 < /dev/null &
echo launched B
