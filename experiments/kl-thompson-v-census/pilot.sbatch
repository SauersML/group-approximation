#!/bin/bash -l
#SBATCH -J hlkl-pilot
#SBATCH -p agsmall
#SBATCH -t 01:30:00
#SBATCH --mem=8G
#SBATCH -c 1
#SBATCH -o /scratch.global/sauer354/hl-kl-counterexample/pilot.%j.log
cd /scratch.global/sauer354/hl-kl-counterexample || exit 1
md5sum certify.py vgroup.py
awk 'NR%283==1' survivors67.txt > pilot_in.txt
wc -l pilot_in.txt
timeout 5000 /usr/bin/python3.12 certify.py pilot_in.txt pilot_out_R${R}.txt ${R} 1,2,3,4
awk '{print $3}' pilot_out_R${R}.txt | sort | uniq -c
grep RETRACT pilot_out_R${R}.txt | head -12
echo DONE
