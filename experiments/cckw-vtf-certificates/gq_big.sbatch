#!/bin/bash -l
#SBATCH -J hrf2-gqbig
#SBATCH -p agsmall
#SBATCH -t 12:00:00
#SBATCH --mem=48G
#SBATCH -c 1
#SBATCH -o /scratch.global/sauer354/hl-hyperbolic-rf-2/logs/gqbig.%j.log
# Lane hl-hyperbolic-rf-2: rerun of one gq_vtf.g task that hit GAP's 12g workspace limit, with 44g.
# Submit with: TAG=334 IDX=26 sbatch --export=ALL gq_big.sbatch   (TAG in 334, 344, 444)
cd /scratch.global/sauer354/hl-hyperbolic-rf-2 || exit 1
module load sagemath/10.7
export DOT_SAGE=/scratch.global/sauer354/hl-hyperbolic-rf-2/dotsage
T=${TAG:?TAG unset}; i=${IDX:?IDX unset}
mkdir -p out
P=out/gq_big_${T}_$i.prelude.g
printf 'INFILE := "cckw%s_q.g";; TARGETFILE := "targets%s_q.g";; ONLY := [%d];;\n' "$T" "$T" "$i" > "$P"
md5sum gq_vtf.g cckw${T}_q.g targets${T}_q.g
timeout 11h sage -gap -q -o 44g "$P" gq_vtf.g < /dev/null > out/gq_big_${T}_$i.out 2>&1
echo EXIT=$? >> out/gq_big_${T}_$i.out
