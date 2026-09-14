#!/bin/bash
#SBATCH --job-name=gk3-control2
#SBATCH --partition=msismall
#SBATCH --nodes=1 --ntasks=1 --cpus-per-task=1 --mem=8G --time=2:00:00
#SBATCH --output=/scratch.global/sauer354/gk3-bernoulli-preservation/run1/run8.%j.log
cd /scratch.global/sauer354/gk3-bernoulli-preservation/run1 || exit 9
module load python/3.10.9_anaconda2023.03_libmamba
echo "start=$(date -Is) host=$(hostname)"; md5sum analyze2.py gp.py dflip.py control2.py analyze3.json flip1.json
python control2.py analyze3.json flip1.json > control2.out.tmp && mv control2.out.tmp control2.out && echo "done=$(date -Is)" && touch DONE8
