#!/bin/bash
#SBATCH --job-name=gk3-tri-dflip
#SBATCH --partition=msismall
#SBATCH --nodes=1 --ntasks=1 --cpus-per-task=1 --mem=16G --time=8:00:00
#SBATCH --output=/scratch.global/sauer354/gk3-bernoulli-preservation/run1/run6.%j.log
cd /scratch.global/sauer354/gk3-bernoulli-preservation/run1 || exit 9
module load python/3.10.9_anaconda2023.03_libmamba
echo "start=$(date -Is) host=$(hostname)"; md5sum analyze2.py gp.py dflip.py flip1.json
python analyze2.py flip1.json > analyze3.json.tmp && mv analyze3.json.tmp analyze3.json && echo "triage done=$(date -Is)" && touch DONE6a || exit 3
python dflip.py analyze3.json flip1.json 3 20000 > dflip3.json.tmp && mv dflip3.json.tmp dflip3.json && echo "dflip done=$(date -Is)" && touch DONE6
