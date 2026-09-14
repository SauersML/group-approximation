#!/bin/bash
#SBATCH --job-name=ac-fs-rescue
#SBATCH --partition=agsmall
#SBATCH --account=hsiehph
#SBATCH --nodes=1
#SBATCH --ntasks=1
#SBATCH --cpus-per-task=17
#SBATCH --mem=16G
#SBATCH --time=04:00:00
#SBATCH --output=/scratch.global/sauer354/hl-andrews-curtis/fs/rescue-%j.log
set -uo pipefail
D=/scratch.global/sauer354/hl-andrews-curtis/fs
cd $D
PY=/usr/bin/python3.12
$PY fsac.py rescue "certs-t4.jsonl" rescue-t4.jsonl > rstats-t4.json &
for s in $(seq 0 15); do $PY fsac.py rescue "certs-t5-s$s.jsonl" rescue-t5-s$s.jsonl > rstats-t5-s$s.json & done
wait
cat rstats-t4.json rstats-t5-s*.json
echo RESCUE_DONE
