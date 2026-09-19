#!/bin/bash
#SBATCH -J bhfinf-cfg
#SBATCH -p ag2tb,msismall
#SBATCH -c 4
#SBATCH --mem=12G
#SBATCH --time=00:20:00
#SBATCH -o /projects/standard/hsiehph/sauer354/bh-finf-hyp/cfg-%j.out
#SBATCH -e /projects/standard/hsiehph/sauer354/bh-finf-hyp/cfg-%j.err
set -u
cd /projects/standard/hsiehph/sauer354/bh-finf-hyp || exit 1
PY=/usr/bin/python3.11
[ -x "$PY" ] || PY=$(command -v python3)
echo "host $(hostname) python $PY start $(date)"
"$PY" -u cfg_test.py 4
echo "end $(date) rc=$?"
