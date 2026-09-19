#!/bin/bash
#SBATCH -p ag2tb,msismall
#SBATCH -c 2
#SBATCH --mem 8G
#SBATCH --time 20:00
#SBATCH -J bhoutfn2b
#SBATCH -o /projects/standard/hsiehph/sauer354/bh-outfn-2/job2-%j.out
cd /projects/standard/hsiehph/sauer354/bh-outfn-2 || exit 1
PY=/usr/bin/python3.11
$PY -c 'import py_compile; py_compile.compile("density.py", doraise=True)' || exit 2
$PY density.py 2 20000 90 dens2.json 24
$PY density.py 3 60000 560 dens3.json 22
rm -rf __pycache__
echo DONE
