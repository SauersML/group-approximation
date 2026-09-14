#!/bin/bash -l
#SBATCH -J mgb-lgdbg
#SBATCH -p agsmall
#SBATCH -t 00:20:00
#SBATCH --mem=2G
#SBATCH -c 1
#SBATCH -o /scratch.global/sauer354/magnus-builder/lgdbg.%j.log
cd /scratch.global/sauer354/magnus-builder || exit 1
md5sum lintongraph.py
LG_VERBOSE=1 timeout 600 /usr/bin/python3.12 lintongraph.py calib 2>&1
echo ALLDONE
