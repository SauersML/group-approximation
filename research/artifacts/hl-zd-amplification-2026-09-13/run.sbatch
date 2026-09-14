#!/bin/bash
#SBATCH --job-name=zdamp-sc
#SBATCH --array=1-8
#SBATCH --time=00:40:00
#SBATCH --mem=2G
#SBATCH --cpus-per-task=1
#SBATCH --output=/scratch.global/sauer354/hl-zd-amplification/search/out.%A.%a.txt
cd /scratch.global/sauer354/hl-zd-amplification/search
K=$(( 10 + 2*SLURM_ARRAY_TASK_ID ))
/usr/bin/python3.12 sc_search.py $SLURM_ARRAY_TASK_ID $K 300
