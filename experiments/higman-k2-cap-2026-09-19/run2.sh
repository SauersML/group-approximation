#!/bin/sh
# usage: run2.sh NAME CLASS "extra relators" "WORDS"
# Like run.sh (chunked lower exponent-2 central quotients P_cl of X = H4(3)/<<[a,c]^2, EXTRA>> with the
# standalone ANU pq, each chunk one `nice -n 10 timeout 1200` process), and after every class it collects
# each word of WORDS (space separated, in the pcp generators x1..x4 = images of a,b,c,d) in P_cl.
# Log NAME.out gets lines "class CL word W: IDENTITY" or "class CL word W: NONTRIVIAL (len L)".
PQ=/tmp/claude-0/-home-user-group-approximation/cfda3a9f-8576-509e-963c-f9b8ce875a39/scratchpad/pq_bin
cd "$(dirname "$0")"; N=$1; T=$2; W="$4"
REL="{b^a*b^-3, c^b*c^-3, d^c*d^-3, a^d*a^-3, [a,c]^2$3}"
last() { ls $N.save_* 2>/dev/null | sed "s/$N.save_//" | sort -n | tail -1; }
col() { printf '8\n'; for w in $W; do printf '23\n%s;\n' "$w"; done; printf '31\n'; }
[ -f $N.out ] || echo "# $N: relators $REL; words $W" > $N.out
while :; do
  k=$(last)
  if [ -z "$k" ]; then
    S0=$(( T < 8 ? T : 8 ))
    { printf '1\nG\n2\n1\n1\n{a, b, c, d}\n%s\n0\n\n' "$REL"; col
      for c in $(seq 2 $S0); do printf '6\n'; col; done; printf '2\n%s.save_%s\n0\n' $N $S0; } > $N.in
  else
    [ "$k" -ge "$T" ] && break
    { printf '3\n%s.save_%s\n' $N $k
      for c in $(seq $((k+1)) $T); do printf '6\n2\n%s.save_%s\n' $N $c; col; done; printf '0\n'; } > $N.in
  fi
  nice -n 10 timeout 1200 $PQ -s 450000000 < $N.in > $N.raw 2>&1; rc=$?
  awk -v W="$W" 'BEGIN{n=split(W,ws," ")}
    /lower exponent-2 central class/ {cl=$NF; for(i=1;i<=NF;i++) if($i=="class") cl=$(i+1); print; i0=0}
    /took/ {print}
    /rror|nsufficient/ {print}
    /result of collection/ {i0++; if ($0 ~ /IDENTITY/) r="IDENTITY"; else r="NONTRIVIAL (len " NF-5 ")";
       print "class " cl " word " ws[i0] ": " r}' $N.raw >> $N.out
  echo "chunk exit $rc $(date -u +%T)" >> $N.out
  k2=$(last); for f in $(ls $N.save_* 2>/dev/null | sed "s/$N.save_//" | sort -n | head -n -1); do rm -f $N.save_$f; done
  [ "$k2" = "$k" ] && { echo "NO PROGRESS at $k" >> $N.out; break; }
done
rm -f $N.raw $N.in
