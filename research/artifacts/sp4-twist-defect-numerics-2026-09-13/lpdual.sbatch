#!/bin/bash -l
#SBATCH -J nh-lpdual
#SBATCH -p agsmall
#SBATCH -t 00:30:00
#SBATCH --mem=6G
#SBATCH -c 1
#SBATCH -o /projects/standard/hsiehph/sauer354/nhnum/lpdual.%j.log
cd /projects/standard/hsiehph/sauer354/nhnum || exit 1
md5sum lp_dual_exact.py pres6.json
python3 lp_dual_exact.py pres6.json
echo "== rc=$?"
echo ALLDONE
