module load python3
cd /projects/standard/hsiehph/sauer354/maslov_experiment
export OMP_NUM_THREADS=4 OPENBLAS_NUM_THREADS=4
mkdir -p analyze
for f in best_m3_seed_seed_theta_d10.json_d10_eps0.2_seed7.npy best_m3_seed_seed_theta_x2_d20.json_d20_eps0.2_seed7.npy best_m3_seed_seed_theta_sum2_d20.json_d20_eps0.2_seed7.npy; do
  python3 analyze_min.py $f 3 seed_theta_d10.json > analyze/$(basename $f .npy).txt 2>&1
done
echo analyze done
