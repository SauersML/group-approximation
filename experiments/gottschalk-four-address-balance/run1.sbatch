#!/bin/bash
#SBATCH --job-name=gk3-flip1
#SBATCH --partition=msismall
#SBATCH --nodes=1 --ntasks=1 --cpus-per-task=1 --mem=8G --time=2:00:00
#SBATCH --output=/scratch.global/sauer354/gk3-bernoulli-preservation/run1/run1.%j.log
cd /scratch.global/sauer354/gk3-bernoulli-preservation/run1 || exit 9
echo "start=$(date -Is) host=$(hostname)"
md5sum flip1.py
/usr/bin/python3.12 flip1.py > flip1.json.tmp && mv flip1.json.tmp flip1.json && echo "done=$(date -Is)" && touch DONE
