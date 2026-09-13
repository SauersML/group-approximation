#!/bin/bash
# Residue rows 18 and 29 of the |w| = 15 table: Nielsen images and an index-13 search.
# 1. images.py: automorphic images of length <= 17, one per symmetry class (same group,
#    different presentation complex, so a different certificate search).
# 2. vfib.py on every image, index <= 8, RPOT = 1, LAM = 2 (14 jobs).
# 3. vfib.py on the two original relators at index 13 only (2 jobs), in parallel with 2.
set -u
cd "$(dirname "$0")"
W18=AAtatATTattaaTT
W29=AAttATaTAttaaTT
python3.11 images.py 17 $W18 $W29 > images1829.out 2>&1
awk '/^IMG/{print $3}' images1829.out | sort -u | head -n 240 > words1829img.txt
mkdir -p vimg vf13
( printf "%s\n%s\n" $W18 $W29 | xargs -P 2 -I{} sh -c "python3.11 vfib.py {} 13 1 2 13 > vf13/{}.out 2>&1"
  echo SWEEP_DONE > vf13/SWEEP_DONE ) &
xargs -a words1829img.txt -P 14 -I{} sh -c "python3.11 vfib.py {} 8 1 2 1 > vimg/{}.out 2>&1"
echo SWEEP_DONE > vimg/SWEEP_DONE
wait
echo PIPE_DONE > pipe1829.done
