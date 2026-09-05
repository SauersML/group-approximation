module load python3
cd /projects/standard/hsiehph/sauer354/maslov_experiment
export OMP_NUM_THREADS=4 OPENBLAS_NUM_THREADS=4
mkdir -p v7eval
seedfor() { case "$1" in *theta_d4_abmin.json_d4_*) echo seed_theta_d4_abmin.json;; *4p4_d8*) echo seed_theta_4p4_d8_abmin.json;; *theta_d10_abmin.json_d10_*) echo seed_theta_d10_abmin.json;; *4x3_d12*) echo seed_theta_4x3_d12_abmin.json;; *10p4_d14*) echo seed_theta_10p4_d14_abmin.json;; *10p10_d20*) echo seed_theta_10p10_d20_abmin.json;; *x2_d20*) echo seed_theta_x2_d20.json;; *) echo none;; esac; }
for f in best7_*.npy; do
  [ -f "$f" ] || continue
  out=v7eval/$(basename $f .npy).txt
  if [ ! -f "$out" ] || [ "$f" -nt "$out" ]; then python3 analyze6.py $f $(seedfor $f) > $out 2>&1; fi
done
for f in v7eval/*.txt; do echo "== $f"; cat $f; done
