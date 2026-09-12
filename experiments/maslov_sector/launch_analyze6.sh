module load python3
cd /projects/standard/hsiehph/sauer354/maslov_experiment
export OMP_NUM_THREADS=4 OPENBLAS_NUM_THREADS=4
mkdir -p v6eval
seedfor() { case "$1" in *theta_d4.json_d4_*) echo seed_theta_d4.json;; *4p4_d8*) echo seed_theta_4p4_d8.json;; *theta_d10.json_d10_*) echo seed_theta_d10.json;; *4x3_d12*) echo seed_theta_4x3_d12.json;; *10p4_d14*) echo seed_theta_10p4_d14.json;; *10p10_d20*) echo seed_theta_10p10_d20.json;; *x2_d20*) echo seed_theta_x2_d20.json;; *) echo none;; esac; }
for f in best6_*.npy; do
  [ -f "$f" ] || continue
  out=v6eval/$(basename $f .npy).txt
  if [ ! -f "$out" ] || [ "$f" -nt "$out" ]; then python3 analyze6.py $f $(seedfor $f) > $out 2>&1; fi
done
for f in v6eval/*.txt; do echo "== $f"; cat $f; done
