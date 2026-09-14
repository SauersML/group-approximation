#!/bin/bash -l
#SBATCH -J hlkl-retract
#SBATCH -p agsmall
#SBATCH -t 04:00:00
#SBATCH --mem=8G
#SBATCH -c 1
#SBATCH --array=0-39%20
#SBATCH -o /scratch.global/sauer354/hl-kl-counterexample/logs/retract.%A_%a.log
cd /scratch.global/sauer354/hl-kl-counterexample || exit 1
P=$(printf "part_%03d" "$SLURM_ARRAY_TASK_ID")
md5sum certify.py vgroup.py rchunks/$P
timeout 13800 /usr/bin/python3.12 certify.py rchunks/$P rresults/$P ${R} 1,2,3,4
echo "lines in results: $(wc -l < rresults/$P) / $(wc -l < rchunks/$P)"
echo DONE
