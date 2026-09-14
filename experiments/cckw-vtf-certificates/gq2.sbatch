#!/bin/bash -l
#SBATCH -J hrf2-gq2
#SBATCH -p agsmall
#SBATCH -t 12:00:00
#SBATCH --mem=16G
#SBATCH -c 1
#SBATCH -o /scratch.global/sauer354/hl-hyperbolic-rf-2/logs/gq2.%A_%a.log
# Lane hl-hyperbolic-rf-2: gq_vtf.g on the VTF-"?" CCKW groups of another half-girth table.
# Submit with: sbatch --array=1-16%3 --export=ALL,TAG=344 gq2.sbatch   (TAG in 344, 444)
cd /scratch.global/sauer354/hl-hyperbolic-rf-2 || exit 1
module load sagemath/10.7
export DOT_SAGE=/scratch.global/sauer354/hl-hyperbolic-rf-2/dotsage
i=$SLURM_ARRAY_TASK_ID
T=${TAG:?TAG unset}
mkdir -p out
P=out/gq_${T}_$i.prelude.g
printf 'INFILE := "cckw%s_q.g";; TARGETFILE := "targets%s_q.g";; ONLY := [%d];;\n' "$T" "$T" "$i" > "$P"
md5sum gq_vtf.g cckw${T}_q.g targets${T}_q.g
timeout 11h sage -gap -q -o 12g "$P" gq_vtf.g < /dev/null > out/gq_${T}_$i.out 2>&1
echo EXIT=$? >> out/gq_${T}_$i.out
