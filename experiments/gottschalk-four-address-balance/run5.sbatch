#!/bin/bash
#SBATCH --job-name=gk3-control1
#SBATCH --partition=msismall
#SBATCH --nodes=1 --ntasks=1 --cpus-per-task=1 --mem=4G --time=2:00:00
#SBATCH --output=/scratch.global/sauer354/gk3-bernoulli-preservation/run1/run5.%j.log
cd /scratch.global/sauer354/gk3-bernoulli-preservation/run1 || exit 9
echo "start=$(date -Is) host=$(hostname)"; md5sum control1.py flip1.json
/usr/bin/python3.12 control1.py flip1.json 20260914 > control1.out.tmp && mv control1.out.tmp control1.out && echo "done=$(date -Is)" && touch DONE5
