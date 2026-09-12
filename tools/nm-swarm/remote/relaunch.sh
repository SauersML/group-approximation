#!/usr/bin/env bash
# relaunch.sh <SHA> <clone...>   stop the running prep + its SLURM base job, relaunch prep at 64 cpus
cd /projects/standard/__MSI_GROUP__/__MSI_USER__/nm || exit 2
pkill -u __MSI_USER__ -f "[b]ash prep.sh"; sleep 2
for j in $(squeue -u __MSI_USER__ -n nm-base -h -o %i); do scancel "$j"; echo "scancel $j"; done
sleep 8
T=$(date +%m%d-%H%M%S)
PREP_CPUS=64 PREP_TIME=05:00:00 setsid nohup bash prep.sh "$@" > "prep-$T.log" 2>&1 < /dev/null &
sleep 40
echo "log prep-$T.log"; tail -3 "prep-$T.log"
squeue -u __MSI_USER__ -n nm-base -o "%.10i %.9P %.8T %.10M %.6C %R"
echo SENTINEL
