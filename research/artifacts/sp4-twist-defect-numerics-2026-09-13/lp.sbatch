#!/bin/bash -l
#SBATCH -J nh-lpkappa
#SBATCH -p agsmall
#SBATCH -t 01:00:00
#SBATCH --mem=8G
#SBATCH -c 1
#SBATCH -o /projects/standard/hsiehph/sauer354/nhnum/lpkappa.%j.log
cd /projects/standard/hsiehph/sauer354/nhnum || exit 1
python3 -c "import scipy, numpy; print('scipy', scipy.__version__, 'numpy', numpy.__version__)"
md5sum lp_kappa.py pres6.json
python3 lp_kappa.py pres6.json
echo "== rc=$?"
echo ALLDONE
