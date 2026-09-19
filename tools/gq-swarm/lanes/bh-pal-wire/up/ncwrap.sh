#!/usr/bin/env bash
# ncwrap.sh FILE: wrap the body of the innermost top namespace in `noncomputable section ... end`.
f=$1
grep -q '^noncomputable section' "$f" && { echo "skip (already) $f"; exit 0; }
L1=$(awk '/^namespace /{last=NR; name=$2; seen=1; next} seen{print last; exit}' "$f")
NAME=$(awk -v l="$L1" 'NR==l{print $2}' "$f")
L2=$(grep -n "^end $NAME\$" "$f" | tail -1 | cut -d: -f1)
[ -n "$L1" ] && [ -n "$L2" ] && [ "$L2" -gt "$L1" ] || { echo "FAILED $f"; exit 1; }
awk -v a="$L1" -v b="$L2" 'NR==b{print "end"; print ""} {print} NR==a{print ""; print "noncomputable section"}' "$f" > "$f.tmp" && mv "$f.tmp" "$f"
echo "wrapped $f ($NAME, lines $L1..$L2)"
