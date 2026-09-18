#!/bin/sh
# Hyperbolicity certificate for G = <a,t | w> with kbmag (Holt): autgroup computes and verifies a
# shortlex automatic structure (gpaxioms); gpgeowa then builds the geodesic word acceptor and
# geodesic pairs machine.  By Papasoglu (Invent. Math. 121 (1995) 323-334), success of gpgeowa
# proves that G is word-hyperbolic.  Usage: kbhyp.sh KBMAGBIN FILE LIMIT  (FILE: relator in first field)
K=$1; F=$2; L=${3:-600}
W=$(mktemp -d)
while read rel rest; do
  [ -z "$rel" ] && continue
  e=$(echo "$rel" | sed 's/./&*/g; s/\*$//')
  printf '_RWS := rec(\n  isRWS := true,\n  ordering := "shortlex",\n  generatorOrder := [a,A,t,T],\n  inverses := [A,a,T,t],\n  equations := [[%s, IdWord]]\n);\n' "$e" > $W/g
  timeout $L $K/autgroup -silent $W/g >/dev/null 2>&1; ra=$?
  if [ $ra -eq 0 ] && [ -f $W/g.success ]; then
    timeout $L $K/gpgeowa -silent $W/g >/dev/null 2>&1; rg=$?
    if [ $rg -eq 0 ] && [ -f $W/g.geowa ]; then
      gs=$(grep -A2 'states := rec' $W/g.geowa | grep -m1 -o 'size := [0-9]*')
      echo "KB $rel AUTOMATIC HYPERBOLIC ($gs geowa)"
    else echo "KB $rel AUTOMATIC GEOWA-FAIL(rc=$rg)"; fi
  else echo "KB $rel AUTGROUP-FAIL(rc=$ra)"; fi
  rm -f $W/g*
done < $F
rmdir $W 2>/dev/null
echo SENTINEL_DONE
