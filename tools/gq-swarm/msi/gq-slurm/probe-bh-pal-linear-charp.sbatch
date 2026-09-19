#!/bin/bash
#SBATCH -p msismall
#SBATCH -c 16
#SBATCH --mem=96G
#SBATCH --time=01:30:00
#SBATCH -J gq-bh-pal-linear-charp
#SBATCH --output=/projects/standard/hsiehph/sauer354/gq-slurm/probe-bh-pal-linear-charp-%j.log
export HOME=/projects/standard/hsiehph/sauer354 XDG_CACHE_HOME=/projects/standard/hsiehph/sauer354/.cache PATH=/projects/standard/hsiehph/sauer354/.elan/bin:$PATH LEAN_NUM_THREADS=16
cd /projects/standard/hsiehph/sauer354/nonsofic_existence || exit 3
exec 9>.lake/fleet-build.lock
flock -w 3600 9 || { echo 'fleet build lock: timed out'; exit 75; }
echo "start $(date) on $(hostname)"
lake build GroupApproximation.BooneHigmanLinear.CharP.LowTrdegCoords GroupApproximation.BooneHigmanLinear.CharP.OneVariableHost
rc=$?
echo "===== RC $rc"
exit $rc
