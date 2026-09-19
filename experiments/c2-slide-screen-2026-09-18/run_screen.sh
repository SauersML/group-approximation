# Stage 1: A5, PSL(2,7) over randomized variants; survivors appended to $SURVIVORS.
for m in perm wins pair perm+wins+pair; do
  nice -n 10 timeout 1200 python3 screen.py A5,PSL27 60 $m 11
done
