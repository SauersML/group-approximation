#!/bin/sh
# for every lattice/g with N in [$1,$2] from scan40.txt, anneal word bound, print ratio word/rect
awk -v a=$1 -v b=$2 '$1>=a && $1<=b' scan40.txt | while read N N1 C g gg d rho s t; do
  N2=$((N/N1)); r=$(./anneal $N1 $N2 $C $g 24 600000 $g); echo "$N $N1 $C $g $d $rho $r"; done
