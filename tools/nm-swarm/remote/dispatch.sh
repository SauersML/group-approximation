#!/usr/bin/env bash
# dispatch.sh <job-script> <outfile> <jobname> [cpus]      (runs ON MSI, reached through `msi`)
#
# Run one build job.  Jobs of <= 8 cpus first try a free 8-core slot on acn112
# (4 slots, cores 64-95: never more than 32 of our cores on the shared node);
# otherwise, and always for bigger jobs, the job goes through SLURM
# (msismall,amdsmall) with --wait.  The job script reads CORES (empty under
# SLURM) and NT (threads) and prints a block starting with "===== SUMMARY".
set -u
JOB=$1; OUT=$2; NAME=$3; CPUS=${4:-8}
NMR=/projects/standard/__MSI_GROUP__/__MSI_USER__/nm
mkdir -p "$NMR/slots"
if [ "$(hostname -s)" = acn112 ] && [ "$CPUS" -le 8 ]; then
  for k in 0 1 2 3; do
    exec {fd}>"$NMR/slots/acn112.$k"
    if flock -n $fd; then
      LO=$((64 + 8*k)); HI=$((LO + 7))
      echo "[dispatch] acn112 slot $k cores $LO-$HI"
      CORES=$LO-$HI NT=8 bash "$JOB" > "$OUT" 2>&1; RC=$?
      sed -n '/^===== SUMMARY/,$p' "$OUT"
      exit $RC
    fi
    exec {fd}>&-
  done
fi
MEM=$(( CPUS * 5 )); [ $MEM -lt 48 ] && MEM=48; [ $MEM -gt 256 ] && MEM=256
STIME=${SLURM_TIME:-04:00:00}
echo "[dispatch] submitting to SLURM msismall,amdsmall ($CPUS cpus, ${MEM}G, $STIME)"
sbatch --wait -p msismall,amdsmall -c "$CPUS" --mem="${MEM}G" -t "$STIME" -J "$NAME" -o "$OUT" \
  --export=ALL,CORES=,NT="$CPUS" --wrap "bash $JOB" > "$OUT.sbatch" 2>&1; RC=$?
cat "$OUT.sbatch"
sed -n '/^===== SUMMARY/,$p' "$OUT"
grep -q '^===== SUMMARY' "$OUT" 2>/dev/null || { echo "===== SUMMARY"; echo "PROBE FAILED: SLURM job produced no summary (infra; rc=$RC)"; tail -5 "$OUT" 2>/dev/null; }
exit $RC
