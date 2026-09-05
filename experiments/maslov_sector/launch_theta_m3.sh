module load python3
cd /projects/standard/hsiehph/sauer354/maslov_experiment
export OMP_NUM_THREADS=4 OPENBLAS_NUM_THREADS=4
python3 make_stacked_seeds.py
mkdir -p thetam3
nohup bash -c "python3 optimize4.py pres6.json 3 seed:seed_theta_d10.json 10 2 600 400 7 1.0 0.2 > thetam3/d10.log 2>&1; python3 eval_all.py best_m3_seed_seed_theta_d10.json_d10_eps0.2_seed7.npy 3 >> thetam3/d10.log 2>&1" < /dev/null > /dev/null 2>&1 &
nohup bash -c "python3 optimize4.py pres6.json 3 seed:seed_theta_x2_d20.json 20 2 600 400 7 1.0 0.2 > thetam3/x2_d20.log 2>&1; python3 eval_all.py best_m3_seed_seed_theta_x2_d20.json_d20_eps0.2_seed7.npy 3 >> thetam3/x2_d20.log 2>&1" < /dev/null > /dev/null 2>&1 &
nohup bash -c "python3 optimize4.py pres6.json 3 seed:seed_theta_sum2_d20.json 20 2 600 400 7 1.0 0.2 > thetam3/sum2_d20.log 2>&1; python3 eval_all.py best_m3_seed_seed_theta_sum2_d20.json_d20_eps0.2_seed7.npy 3 >> thetam3/sum2_d20.log 2>&1" < /dev/null > /dev/null 2>&1 &
nohup bash -c "python3 optimize4.py pres6.json 3 seed:seed_theta_x3_d30.json 30 1 600 300 7 1.0 0.2 > thetam3/x3_d30.log 2>&1; python3 eval_all.py best_m3_seed_seed_theta_x3_d30.json_d30_eps0.2_seed7.npy 3 >> thetam3/x3_d30.log 2>&1" < /dev/null > /dev/null 2>&1 &
sleep 3; ps -u sauer354 -o pid,cmd | grep optimize4 | grep -v grep | wc -l
