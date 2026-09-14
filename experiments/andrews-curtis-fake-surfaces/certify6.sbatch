#!/bin/bash
#SBATCH --job-name=ac-fs-cert6
#SBATCH --partition=agsmall
#SBATCH --account=hsiehph
#SBATCH --nodes=1
#SBATCH --ntasks=1
#SBATCH --cpus-per-task=64
#SBATCH --mem=48G
#SBATCH --time=08:00:00
#SBATCH --output=/scratch.global/sauer354/hl-andrews-curtis/fs/cert6-%j.log
set -uo pipefail
D=/scratch.global/sauer354/hl-andrews-curtis/fs
cd $D
PY=/usr/bin/python3.12
$PY -c "import fsac; print(len(fsac.load_graphs(6)))"
for s in $(seq 0 63); do $PY fsac.py certify classes-t6.txt certs-t6-s$s.jsonl.gz $s 64 > stats-t6-s$s.json & done
wait
$PY -c "
import json,glob,collections
tot=collections.Counter()
for f in glob.glob('stats-t6-s*.json'): tot.update(json.load(open(f)))
print('t6 certify', dict(tot))"
for s in $(seq 0 63); do $PY fsac.py rescue "certs-t6-s$s.jsonl.gz" rescue-t6-s$s.jsonl > rstats-t6-s$s.json & done
wait
$PY -c "
import json,glob,collections
tot=collections.Counter()
for f in glob.glob('rstats-t6-s*.json'): tot.update(json.load(open(f)))
print('t6 rescue', dict(tot))"
for s in $(seq 0 63); do $PY fsac.py rescue2 "rescue-t6-s$s.jsonl" rescue2-t6-s$s.jsonl > r2stats-t6-s$s.json & done
wait
$PY -c "
import json,glob,collections
tot=collections.Counter()
for f in glob.glob('r2stats-t6-s*.json'): tot.update(json.load(open(f)))
print('t6 rescue2', dict(tot))"
for s in $(seq 0 63); do $PY acverify.py certs-t6-s$s.jsonl.gz rescue-t6-s$s.jsonl rescue2-t6-s$s.jsonl > vstats-t6-s$s.json & done
wait
$PY -c "
import json,glob,collections
tot=collections.Counter()
for f in glob.glob('vstats-t6-s*.json'): tot.update(json.load(open(f)))
print('t6 acverify', dict(tot))"
$PY coverage.py 6 classes-t6.txt certs-t6-s*.jsonl.gz rescue-t6-s*.jsonl rescue2-t6-s*.jsonl > coverage-t6.txt
head -3 coverage-t6.txt; grep -c UNCOVERED coverage-t6.txt; grep PI1_NONTRIVIAL coverage-t6.txt | head
echo CERT6_DONE
