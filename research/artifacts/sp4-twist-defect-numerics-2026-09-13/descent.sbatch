#!/bin/bash -l
#SBATCH -J nh-descent2
#SBATCH -p agsmall
#SBATCH -t 05:00:00
#SBATCH --mem=16G
#SBATCH -c 4
#SBATCH -o /projects/standard/hsiehph/sauer354/nhnum/descent2.%j.log
# Larger-d smoothed-maximum descents (optimize7.py from main, unchanged) in the mod-3 sector from stacked metaplectic
# seeds at the coboundary optimum; working-set size and iterations scaled down with d so one restart fits its timeout.
# NUMERICS: upper bounds over a working set; blind by design to countermodels with unbounded irreducible blocks
# (maslov-bounded-block-sector-gap); never evidence of a floor.
cd /projects/standard/hsiehph/sauer354/nhnum || exit 1
export OMP_NUM_THREADS=4 OPENBLAS_NUM_THREADS=4
md5sum optimize7.py make_seeds_nh.py seed_theta_d10.json pres6.json
[ -s seed_theta_x4_d40_abmin.json ] || python3 make_seeds_nh.py 2 3 4
mkdir -p v7nh
# args: pres modulus init d restarts iters n_unl seed beta pin eps0
run() { m=$1; it=$2; nu=$3; d=$((10*m)); t0=$(date +%s)
  timeout 5400 python3 -u optimize7.py pres6.json 3 seed:seed_theta_x${m}_d${d}_abmin.json $d 1 $it $nu $((60+m)) 30 0 0.1 > v7nh/d${d}_b30_eps0.1_it${it}_n${nu}.log 2>&1
  echo "== d=$d iters=$it n_unl=$nu rc=$? seconds=$(( $(date +%s) - t0 ))"; tail -3 v7nh/d${d}_b30_eps0.1_it${it}_n${nu}.log; }
run 2 300 6000
run 3 200 3000
run 4 150 1500
echo ALLDONE
