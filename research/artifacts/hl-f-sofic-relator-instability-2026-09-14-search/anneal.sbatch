#!/bin/bash
#SBATCH --job-name=frho-anneal
#SBATCH --partition=amdsmall
#SBATCH --ntasks=1
#SBATCH --cpus-per-task=16
#SBATCH --mem=4G
#SBATCH --time=01:30:00
#SBATCH --output=/scratch.global/sauer354/hl-f-sofic-relator-instability/fanneal.%j.log
cd /scratch.global/sauer354/hl-f-sofic-relator-instability || exit 1
rm -f anneal.jobs; for m in 8 10 12 16 24 32 48 64 96 128; do for fr in 0.25 0.5 0.75; do for s in 1 2 3 4; do echo "./anneal_ratio $m $fr 3000000 $s" >> anneal.jobs; done; done; done
xargs -P 16 -I{} sh -c "{} | head -1" < anneal.jobs > anneal.out
sort -t= -k2 -n anneal.out > anneal.sorted; echo ALLDONE
