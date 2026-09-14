#!/bin/bash -l
#SBATCH -J bc16-classify
#SBATCH -p agsmall
#SBATCH -t 06:00:00
#SBATCH --mem=12G
#SBATCH -c 1
#SBATCH --array=0-39%8
#SBATCH -o /scratch.global/sauer354/hl-balanced-census-16/logs/classify16.%A_%a.log
# GAP classifier bal.g (unchanged from the certified L <= 15 run) on the L = 16, 17 classes.
cd /scratch.global/sauer354/hl-balanced-census-16 || exit 1
mkdir -p results16
P=$(printf "part_%02d" "$SLURM_ARRAY_TASK_ID")
MAXC=${MAXC:-200000}
MAXIDX=${MAXIDX:-8}
md5sum bal.g chunks16/$P
rm -f results16/$P
cat > run_$P.g <<EOF
Read("bal.g");
RunBal("chunks16/$P", "results16/$P", $MAXC, $MAXIDX);
QUIT;
EOF
timeout 21000 /scratch.global/sauer354/solve-kl-counterexample-search/gap-4.13.1/gap -q -o 10g run_$P.g < /dev/null
echo "lines in results: $(wc -l < results16/$P) / $(wc -l < chunks16/$P)"
echo DONE
