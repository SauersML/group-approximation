#!/bin/bash -l
#SBATCH -J bc16-rccal
#SBATCH -p agsmall
#SBATCH -t 01:00:00
#SBATCH --mem=8G
#SBATCH -c 1
#SBATCH -o /scratch.global/sauer354/hl-balanced-census-16/logs/rc15cal.%j.log
# Calibrate the orbit-counting recount on the certified L <= 15 census, with three negative controls.
cd /scratch.global/sauer354/hl-balanced-census-16 || exit 1
md5sum rc_orbit.py census15.txt
echo "=== census15 (expect MATCH)"
/usr/bin/python3.12 rc_orbit.py census15.txt 2 15
echo "=== control: last line dropped (expect MISMATCH, block 3 12 or similar BAD)"
head -n 24570 census15.txt > ctl_drop.txt
tail -n 1 census15.txt
/usr/bin/python3.12 rc_orbit.py ctl_drop.txt 2 15 | grep -e BAD -e MATCH -e "bad rep"
echo "=== control: last line repeated (expect MISMATCH, repeat)"
cat census15.txt > ctl_dup.txt
tail -n 1 census15.txt >> ctl_dup.txt
/usr/bin/python3.12 rc_orbit.py ctl_dup.txt 2 15 | grep -e BAD -e MATCH -e "bad rep"
echo "=== control: second relator of the last line rotated by one (expect MISMATCH, not-orbit-minimum)"
awk 'NR==24571 { $4 = substr($4, 2) substr($4, 1, 1) } { print }' census15.txt > ctl_rot.txt
tail -n 1 ctl_rot.txt
/usr/bin/python3.12 rc_orbit.py ctl_rot.txt 2 15 | grep -e BAD -e MATCH -e "bad rep"
echo DONE
