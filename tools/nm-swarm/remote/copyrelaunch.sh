#!/usr/bin/env bash
# copyrelaunch.sh <clone...>  stop copynow.sh and its copy children, relaunch copynow2.sh detached
cd /projects/standard/__MSI_GROUP__/__MSI_USER__/nm || exit 2
pkill -u __MSI_USER__ -f "[c]opynow.sh"
pkill -u __MSI_USER__ -f "[r]sync -a --exclude /CharClass/ /projects/standard/__MSI_GROUP__/__MSI_USER__/cc_clones/lead"
pkill -u __MSI_USER__ -f "[r]sync -a --delete /projects/standard/__MSI_GROUP__/__MSI_USER__/cc_clones/lead/GroupApproximation/"
pkill -u __MSI_USER__ -f "[r]m -rf /projects/standard/__MSI_GROUP__/__MSI_USER__/cc_clones/[a-z0-9-]*/.lake/build/"
sleep 5
T=$(date +%m%d-%H%M%S)
setsid nohup bash copynow2.sh "$@" > "copynow2-$T.log" 2>&1 < /dev/null &
sleep 20
echo "log copynow2-$T.log"; tail -3 "copynow2-$T.log"
pgrep -u __MSI_USER__ -fa "[r]sync -a --delete" | wc -l
echo SENTINEL
