#!/bin/bash
# char-2 quaternion search for the (5,3) classes passing the local-action filter: D = [1, t+1) over F_2(t),
# ramified at {t+1, inf}; v-tree at t (valency 3), h-tree at t^2+t+1 (valency 5); coordinates of degree <= 1
cd $(dirname $0)
for pc in 50_30:499 50_30:515 50_31:235 50_31:243 51_30:660 51_30:661 51_31:279 51_31:309 52_30:386 52_31:185; do
  p=${pc%:*}; c=${pc#*:}
  echo "== $p $c"
  nice -n 10 timeout 1200 python3 findquat.py census_$p.json $c 1 1 3 2 7
done
