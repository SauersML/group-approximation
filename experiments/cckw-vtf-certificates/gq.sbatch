#!/bin/bash -l
#SBATCH -J hrf2-gq
#SBATCH -p agsmall
#SBATCH -t 12:00:00
#SBATCH --mem=16G
#SBATCH -c 1
#SBATCH --array=1-53%6
#SBATCH -o /scratch.global/sauer354/hl-hyperbolic-rf-2/logs/gq.%A_%a.log
# Lane hl-hyperbolic-rf-2: epimorphisms of the 53 VTF-"?" CCKW (3,3,4) groups onto their listed simple
# quotients, with single and product vertex-injectivity (gq_vtf.g). One array task per group.
cd /scratch.global/sauer354/hl-hyperbolic-rf-2 || exit 1
module load sagemath/10.7
export DOT_SAGE=/scratch.global/sauer354/hl-hyperbolic-rf-2/dotsage
i=$SLURM_ARRAY_TASK_ID
mkdir -p out
P=out/gq_q_$i.prelude.g
printf 'INFILE := "cckw334_q.g";; TARGETFILE := "targets334_q.g";; ONLY := [%d];;\n' "$i" > "$P"
md5sum gq_vtf.g cckw334_q.g targets334_q.g
timeout 11h sage -gap -q -o 12g "$P" gq_vtf.g < /dev/null > out/gq_q_$i.out 2>&1
echo EXIT=$? >> out/gq_q_$i.out
