#!/bin/bash -l
#SBATCH -J hlkl-thm
#SBATCH -p agsmall
#SBATCH -t 02:00:00
#SBATCH --mem=8G
#SBATCH -c 1
#SBATCH -o /scratch.global/sauer354/hl-kl-counterexample/thm.%j.log
cd /scratch.global/sauer354/hl-kl-counterexample || exit 1
md5sum certify.py vgroup.py survivors67.txt
timeout 7000 /usr/bin/python3.12 certify.py survivors67.txt theorems_out.txt -1 1
wc -l theorems_out.txt
paste -d' ' survivors67.txt theorems_out.txt | awk '{print $3,$4,$5,$8}' | sort | uniq -c
awk '$3=="FRONTIER"' theorems_out.txt > frontier.txt
wc -l frontier.txt
grep -m3 CORNER3 theorems_out.txt; grep -m3 POWER theorems_out.txt
echo DONE
