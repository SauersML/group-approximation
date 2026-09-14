#!/bin/bash
#SBATCH --job-name=kprof-cert8
#SBATCH --time=12:00:00
#SBATCH --mem=24G
#SBATCH --cpus-per-task=1
#SBATCH --array=0-3
#SBATCH --output=/scratch.global/sauer354/hl-f-kernel-profiles/logs/cert8_%A_%a.log
# Explicit degree-8 common multiples a u = b v over F_2 for four sampled P_(2,2) pairs that kprof reports
# settled at degree 8 (unsettled after degree 7 in the landed census), rechecked by composing PL maps
# with ore_verify.py cert (no normal forms). Uses the landed ore_certify.py / ore_verify.py unchanged.
set -u
cd /scratch.global/sauer354/hl-f-kernel-profiles
md5sum ore_linalg.py ore_certify.py ore_verify.py cert8_pairs.json
i=$SLURM_ARRAY_TASK_ID
/usr/bin/python3.12 -c "
import json; d=json.load(open('cert8_pairs.json')); json.dump([d[$i]], open('cert8_in_$i.json','w'))"
t0=$(date +%s)
/usr/bin/python3.12 ore_certify.py S35 cert8_in_$i.json cert8_out_$i.json
echo "certify rc=$? secs=$(( $(date +%s) - t0 ))"
/usr/bin/python3.12 ore_verify.py cert cert8_out_$i.json
echo "verify rc=$? secs=$(( $(date +%s) - t0 ))"
/usr/bin/python3.12 -c "
import json; c=json.load(open('cert8_out_$i.json'))[0]; print('TERMS', c['a'], c['b'], len(c['u']), len(c['v']))"
echo "EXIT $(date)"
