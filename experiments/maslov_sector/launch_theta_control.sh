module load python3
cd /projects/standard/hsiehph/sauer354/maslov_experiment
export OMP_NUM_THREADS=2 OPENBLAS_NUM_THREADS=2
python3 - <<'PY'
import json, numpy as np
R8 = np.load("theta10_generators.npy")
json.dump({"seed": [[[float(z.real), float(z.imag)] for z in row] for U in R8 for row in U], "d": 10}, open("seed_theta_d10.json", "w"))
PY
mkdir -p thetactl
python3 optimize4.py pres6.json 2 seed:seed_theta_d10.json 10 1 5 400 0 1.0 0.0 > thetactl/seed_check.log 2>&1; tail -n 1 thetactl/seed_check.log
for e in 0.5 1.0 1.5; do nohup python3 optimize4.py pres6.json 2 seed:seed_theta_d10.json 10 3 600 400 7 1.0 $e > thetactl/basin_m2_eps$e.log 2>&1 < /dev/null & done
for e in 0.2 0.5 1.0; do nohup python3 optimize4.py pres6.json 3 seed:seed_theta_d10.json 10 4 600 400 7 1.0 $e > thetactl/m3_from_theta_eps$e.log 2>&1 < /dev/null & done
sleep 2; ps -u sauer354 -o pid,cmd | grep optimize4 | grep -v grep | wc -l
