#!/bin/bash
#SBATCH -p ag2tb,msismall
#SBATCH -c 2
#SBATCH --mem 8G
#SBATCH --time 30:00
#SBATCH -J bhoutfn2
#SBATCH -o /projects/standard/hsiehph/sauer354/bh-outfn-2/job-%j.out
cd /projects/standard/hsiehph/sauer354/bh-outfn-2 || exit 1
PY=$(command -v python3.11 || command -v python3)
echo "python: $PY"; $PY -c 'import py_compile; py_compile.compile("spheres.py", doraise=True)' || exit 2
$PY spheres.py 2 3000 240 rank2.json
$PY spheres.py 3 8000 1200 rank3.json
echo DONE
