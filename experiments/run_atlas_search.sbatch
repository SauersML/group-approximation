#!/usr/bin/env bash
#SBATCH --job-name=atlas2chart
#SBATCH --partition=sioux
#SBATCH --nodelist=acn116
#SBATCH --nodes=1
#SBATCH --ntasks=1
#SBATCH --cpus-per-task=4
#SBATCH --mem=8G
#SBATCH --time=00:20:00
#SBATCH --output=atlas-search-%j.log

set -euo pipefail

export OPENBLAS_NUM_THREADS=4
export OMP_NUM_THREADS=4

cd "${SLURM_SUBMIT_DIR:?submit this job from the repository root}"

seed_dir="experiments/atlas-run-${SLURM_JOB_ID}"
mkdir -p "$seed_dir"

python3 experiments/atlas_two_chart_search.py \
  --k 1 --iters 600 --seeds 3 --batch 48 --report-every 100 \
  --save "$seed_dir/k1-mean.npy"
python3 experiments/atlas_two_chart_search.py \
  --k 2 --iters 300 --seeds 2 --batch 40 --report-every 75 \
  --init "$seed_dir/k1-mean.npy" --save "$seed_dir/k2-mean.npy"

# Minimize the worst tail separately.  These runs intentionally trade mean
# loss for a lower maximum loss and start from the mean-optimized seeds.
python3 experiments/atlas_two_chart_search.py \
  --k 1 --iters 180 --seeds 1 --batch 32 --report-every 30 \
  --focus-every 5 --init "$seed_dir/k1-mean.npy" \
  --save "$seed_dir/k1-focus.npy"
python3 experiments/atlas_two_chart_search.py \
  --k 2 --iters 150 --seeds 1 --batch 32 --report-every 30 \
  --focus-every 5 --init "$seed_dir/k2-mean.npy" \
  --save "$seed_dir/k2-focus.npy"
python3 experiments/atlas_two_chart_search.py \
  --k 4 --iters 120 --seeds 1 --batch 32 --report-every 30 \
  --focus-every 5 --init "$seed_dir/k2-mean.npy" \
  --save "$seed_dir/k4-focus.npy"
