module load python3
cd /projects/standard/hsiehph/sauer354/maslov_experiment
export OMP_NUM_THREADS=4 OPENBLAS_NUM_THREADS=4
mkdir -p v5eval
for f in best5_*.npy; do
  [ -f "$f" ] || continue
  out=v5eval/$(basename $f .npy).txt
  if [ ! -f "$out" ] || [ "$f" -nt "$out" ]; then python3 eval_all.py $f 3 > $out 2>&1; fi
done
cat v5eval/*.txt 2>/dev/null
