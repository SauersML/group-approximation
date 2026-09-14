#!/bin/bash
#SBATCH --job-name=frho-seeded
#SBATCH --partition=amdsmall
#SBATCH --ntasks=1
#SBATCH --cpus-per-task=16
#SBATCH --mem=4G
#SBATCH --time=01:30:00
#SBATCH --output=/scratch.global/sauer354/hl-f-sofic-relator-instability/fseeded.%j.log
cd /scratch.global/sauer354/hl-f-sofic-relator-instability || exit 1
xargs -P 16 -I{} sh -c "{}" < sa.jobs
grep -h best sa.*.txt | sort -t= -k2 -n > sa.summary; echo ALLDONE
