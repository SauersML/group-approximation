#!/bin/bash
#SBATCH --job-name=ac-fs-cert15
#SBATCH --partition=agsmall
#SBATCH --account=hsiehph
#SBATCH --nodes=1
#SBATCH --ntasks=1
#SBATCH --cpus-per-task=16
#SBATCH --mem=16G
#SBATCH --time=02:00:00
#SBATCH --output=/scratch.global/sauer354/hl-andrews-curtis/fs/cert15-%j.log
set -uo pipefail
D=/scratch.global/sauer354/hl-andrews-curtis/fs
cd $D
PY=/usr/bin/python3.12
for t in 1 2 3 4 5; do $PY fsac.py graphs $t > graphs-t$t.txt; $PY -c "import fsac; fsac.load_graphs($t)"; done
for t in 1 2 3 4; do $PY fsac.py certify classes-t$t.txt certs-t$t.jsonl 0 1 | sed "s/^/t=$t /"; done
for s in $(seq 0 15); do $PY fsac.py certify classes-t5.txt certs-t5-s$s.jsonl $s 16 > stats-t5-s$s.json & done
wait
cat stats-t5-s*.json
echo CERT15_DONE
