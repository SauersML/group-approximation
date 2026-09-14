#!/bin/bash -l
#SBATCH -J hrf2-lins
#SBATCH -p agsmall
#SBATCH -t 12:00:00
#SBATCH --mem=16G
#SBATCH -c 1
#SBATCH --array=1-53%6
#SBATCH -o /scratch.global/sauer354/hl-hyperbolic-rf-2/logs/lins.%A_%a.log
# Lane hl-hyperbolic-rf-2: all normal subgroups of index <= BOUND (LINS) of the 53 VTF-"?" CCKW (3,3,4)
# groups, with single and product vertex-injectivity (lins_vtf.g). One array task per group.
# Submit with: sbatch --export=ALL,BOUND=10000 lins.sbatch
cd /scratch.global/sauer354/hl-hyperbolic-rf-2 || exit 1
module load sagemath/10.7
export DOT_SAGE=/scratch.global/sauer354/hl-hyperbolic-rf-2/dotsage
i=$SLURM_ARRAY_TASK_ID
B=${BOUND:-10000}
mkdir -p out
P=out/lins_q_${B}_$i.prelude.g
printf 'INFILE := "cckw334_q.g";; INDEXBOUND := %d;; ONLY := [%d];;\n' "$B" "$i" > "$P"
md5sum lins_vtf.g cckw334_q.g
timeout 11h sage -gap -q -o 12g -l ";/scratch.global/sauer354/hl-hyperbolic-rf-2/gaproot" "$P" lins_vtf.g < /dev/null > out/lins_q_${B}_$i.out 2>&1
echo EXIT=$? >> out/lins_q_${B}_$i.out
