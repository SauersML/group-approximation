#!/bin/bash
#SBATCH --job-name=gk3b-ctl
#SBATCH --time=01:00:00
#SBATCH --mem=8G
#SBATCH --cpus-per-task=1
#SBATCH --output=/scratch.global/sauer354/gk3-ternary-bilinear/runs/ctl-%j.log
set -euo pipefail
D=/scratch.global/sauer354/gk3-ternary-bilinear
cd $D/code
$D/venv/bin/python bscreen.py --mode controls --out $D/runs/controls.json
echo EXIT=$?
