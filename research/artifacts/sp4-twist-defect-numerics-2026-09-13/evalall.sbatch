#!/bin/bash -l
#SBATCH -J nh-evalall
#SBATCH -p agsmall
#SBATCH -t 03:00:00
#SBATCH --mem=12G
#SBATCH -c 4
#SBATCH -o /projects/standard/hsiehph/sauer354/nhnum/evalall.%j.log
# All-relator evaluation of the d = 20, 30, 40 descent minima and their start points.
# NUMERICS: upper bounds over the length-13 window only; never a lower bound or evidence of a sector floor.
cd /projects/standard/hsiehph/sauer354/nhnum || exit 1
export OMP_NUM_THREADS=4 OPENBLAS_NUM_THREADS=4
md5sum eval_descent_all.py pres6.json seed_theta_d10.json
T="seed_theta_x2_d20_abmin.json best7_m3_seed_seed_theta_x2_d20_abmin.json_d20_p30.0_pin0_eps0.1_seed62.npy seed_theta_x3_d30_abmin.json best7_m3_seed_seed_theta_x3_d30_abmin.json_d30_p30.0_pin0_eps0.1_seed63.npy seed_theta_x4_d40_abmin.json best7_m3_seed_seed_theta_x4_d40_abmin.json_d40_p30.0_pin0_eps0.1_seed64.npy"
ls -la $T
python3 -u eval_descent_all.py pres6.json seed_theta_d10.json $T
echo "== rc=$?"
echo ALLDONE
