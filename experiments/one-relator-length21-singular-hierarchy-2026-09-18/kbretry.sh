#!/bin/sh
# Retry kbhyp.sh on relators whose first attempt failed, after renaming a<->t (an isomorphic
# presentation; equivalently the shortlex order [t,T,a,A]).  Output lines are "KB <swapped> ..."
# followed by "ORIG <original>" so each result can be traced back.  Usage: kbretry.sh FAILFILE LIMIT
K=/tmp/claude-0/-home-user-group-approximation/cfda3a9f-8576-509e-963c-f9b8ce875a39/scratchpad/sw104-build/kbmag/bin/x86
L=${2:-300}
while read rel rest; do
  [ -z "$rel" ] && continue
  sw=$(echo "$rel" | tr 'aAtT' 'tTaA')
  echo "$sw" > kbretry1.$$
  sh ../one-relator-top-magnus-intersection-2026-09-18/kbhyp.sh $K kbretry1.$$ $L | grep '^KB' | sed "s/\$/ ORIG $rel/"
done < $1
rm -f kbretry1.$$
echo SENTINEL_DONE
