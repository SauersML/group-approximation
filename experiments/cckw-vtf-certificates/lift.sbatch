#!/bin/bash -l
#SBATCH -J hrf2-lift
#SBATCH -p agsmall
#SBATCH -t 06:00:00
#SBATCH --mem=24G
#SBATCH -c 1
#SBATCH --array=1-13%6
#SBATCH -o /scratch.global/sauer354/hl-hyperbolic-rf-2/logs/lift.%A_%a.log
# Lane hl-hyperbolic-rf-2: lift epimorphisms onto listed simple quotients to quasisimple covers
# (lift_vtf.g, specs in lift_specs.g); vertex-injective lifts are exported and checked with verify_vtf_cert.py.
cd /scratch.global/sauer354/hl-hyperbolic-rf-2 || exit 1
module load sagemath/10.7
export DOT_SAGE=/scratch.global/sauer354/hl-hyperbolic-rf-2/dotsage
i=$SLURM_ARRAY_TASK_ID
mkdir -p out certs
P=out/lift_$i.prelude.g
printf 'SPECFILE := "lift_specs.g";; SPECINDEX := %d;;\n' "$i" > "$P"
md5sum lift_vtf.g lift_specs.g verify_vtf_cert.py cckw334_q.g cckw344_q.g
timeout 5h sage -gap -q -o 22g "$P" lift_vtf.g < /dev/null > out/lift_$i.out 2>&1
echo EXIT=$? >> out/lift_$i.out
for f in $(grep -o 'certs/[A-Za-z0-9_]*_lift[0-9]*\.cert' out/lift_$i.out | sort -u); do
  /usr/bin/python3.12 verify_vtf_cert.py "$f" >> out/lift_verify_$i.out 2>&1
  echo "EXIT=$? $f" >> out/lift_verify_$i.out
  md5sum "$f" >> out/lift_verify_$i.out
done
echo LIFT_JOB_DONE >> out/lift_verify_$i.out
