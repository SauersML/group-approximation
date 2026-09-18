#!/usr/bin/env bash
# Lower exponent-p central tower of Gamma^A2_p = <a,b,c | a^p,b^p,c^p, Heisenberg relations on ab, bc, ca>
# with the standalone ANU p-Quotient program (source: GAP package anupq 3.x, src/ and include/).
#
# Build (once), from an empty directory next to the anupq checkout:
#   printf '#define HAVE_UNISTD_H 1\n#define HAVE_STRFTIME 1\n#define HAVE_GETHOSTNAME 1\n#define PQ_GAP_EXEC "gap"\n#define PQ_VERSION "1.9"\n#define PACKAGE_VERSION "1.9"\n' > config.h
#   gcc -O2 -w -I. -I<anupq>/include -DGAP_LINK_VIA_FILE -DGAP -DSTANDARD_PCP -DGROUP \
#       -DANUPQ_GAP_EXEC='"gap"' <anupq>/src/*.c -o pq -lm
#
# Usage: pqtower.sh <pq binary> p class [w]
#   With the optional fourth argument "w", the relator w_p=([b,a][b,c])^p is added.
# Prints the orders p^n of the class-k quotients; I_1/P_{k+1}(I_1) has order p^(3,6,8,11,14,16,...) (increments 3,3,2).
pq=$1; p=$2; c=$3; extra=""
[ "$4" = w ] && extra=", ([b,a]*[b,c])^$p"
printf '1\nG\n%s\n%s\n1\n{a, b, c}\n{a^%s, b^%s, c^%s, [a,b,a], [a,b,b], [b,c,b], [b,c,c], [a,c,a], [a,c,c]%s}\n0\n\n0\n' \
  "$p" "$c" "$p" "$p" "$p" "$extra" | "$pq" | grep -E "has order|took|Total user time"
