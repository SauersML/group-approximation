#!/bin/bash
#SBATCH --job-name=gk3-analyze2
#SBATCH --partition=msismall
#SBATCH --nodes=1 --ntasks=1 --cpus-per-task=1 --mem=16G --time=3:00:00
#SBATCH --output=/scratch.global/sauer354/gk3-bernoulli-preservation/run1/run3.%j.log
cd /scratch.global/sauer354/gk3-bernoulli-preservation/run1 || exit 9
module load python/3.10.9_anaconda2023.03_libmamba
echo "start=$(date -Is) host=$(hostname)"; md5sum analyze2.py flip1.json
python analyze2.py flip1.json > analyze2.json.tmp && mv analyze2.json.tmp analyze2.json && echo "done=$(date -Is)" && touch DONE3
