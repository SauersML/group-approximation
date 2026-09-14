#!/bin/bash -l
#SBATCH -J hlkl-collapse
#SBATCH -p agsmall
#SBATCH -t 04:00:00
#SBATCH --mem=12G
#SBATCH -c 1
#SBATCH --array=0-39%20
#SBATCH -o /scratch.global/sauer354/hl-kl-counterexample/logs/collapse.%A_%a.log
cd /scratch.global/sauer354/hl-kl-counterexample || exit 1
P=$(printf "part_%03d" "$SLURM_ARRAY_TASK_ID")
MAXC=${MAXC:-200000}
md5sum klcx.g chunks/$P
cat > run_$P.g <<EOF
Read("klcx.g");
RunFile("chunks/$P", "results/$P", $MAXC);
QUIT;
EOF
timeout 13800 ./gap-4.13.1/gap -q -o 10g run_$P.g < /dev/null
echo "lines in results: $(wc -l < results/$P) / $(wc -l < chunks/$P)"
echo DONE
