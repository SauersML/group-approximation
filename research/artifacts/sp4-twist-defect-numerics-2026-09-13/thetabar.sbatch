#!/bin/bash -l
#SBATCH -J nh-thetabar
#SBATCH -p agsmall
#SBATCH -t 03:00:00
#SBATCH --mem=24G
#SBATCH -c 1
#SBATCH -o /projects/standard/hsiehph/sauer354/nhnum/thetabar.%j.log
cd /projects/standard/hsiehph/sauer354/nhnum || exit 1
python3 -V; python3 -c "import numpy; print('numpy', numpy.__version__)"
md5sum presentation.py theta_bar_profile.py
t0=$(date +%s)
[ -s pres6.json ] || python3 presentation.py 6 13 pres6.json
echo "== presentation done rc=$? seconds=$(( $(date +%s) - t0 )) size=$(stat -c %s pres6.json 2>/dev/null)"
python3 theta_bar_profile.py pres6.json theta_bar_profile.tsv
echo "== profile rc=$? seconds=$(( $(date +%s) - t0 ))"
echo ALLDONE
