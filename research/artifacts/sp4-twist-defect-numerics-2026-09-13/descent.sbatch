#!/bin/bash -l
#SBATCH -J nh-descent
#SBATCH -p agsmall
#SBATCH -t 04:00:00
#SBATCH --mem=16G
#SBATCH -c 4
#SBATCH -o /projects/standard/hsiehph/sauer354/nhnum/descent.%j.log
# Larger-d smoothed-maximum descents (optimize7.py from main, unchanged) in the mod-3 sector from stacked metaplectic
# seeds at the coboundary optimum.  NUMERICS: upper bounds on relator defects over a working set; blind by design to
# countermodels with unbounded irreducible blocks (maslov-bounded-block-sector-gap); never evidence of a floor.
cd /projects/standard/hsiehph/sauer354/nhnum || exit 1
export OMP_NUM_THREADS=4 OPENBLAS_NUM_THREADS=4
md5sum optimize7.py make_seeds_nh.py seed_theta_d10.json pres6.json
python3 make_seeds_nh.py 2 3 4
mkdir -p v7nh
# args: pres modulus init d restarts iters n_unl seed beta pin eps0
for m in 2 3 4; do
  d=$((10*m)); t0=$(date +%s)
  timeout 4200 python3 optimize7.py pres6.json 3 seed:seed_theta_x${m}_d${d}_abmin.json $d 1 300 6000 $((60+m)) 30 0 0.1 > v7nh/d${d}_b30_eps0.1.log 2>&1
  echo "== d=$d rc=$? seconds=$(( $(date +%s) - t0 ))"; tail -4 v7nh/d${d}_b30_eps0.1.log
done
echo ALLDONE
