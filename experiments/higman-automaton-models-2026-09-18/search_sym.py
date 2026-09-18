# Search cyclically symmetric wreath recursions for H4(n) on the binary tree:
#   a = (u, v) pi, b = sigma(u, v) pi, c = sigma^2(...), d = sigma^3(...),
# sigma : a -> b -> c -> d -> a.  u, v range over reduced words of length <= MAXLEN.
# Survivors: all four Higman relations hold on levels 1..LCHK. Reports orders of a on levels.
import sys
from ss_core import *

n = int(sys.argv[1]) if len(sys.argv) > 1 else 3
MAXLEN = int(sys.argv[2]) if len(sys.argv) > 2 else 3
LCHK = int(sys.argv[3]) if len(sys.argv) > 3 else 10
rels = higman_rels(n)
W = reduced_words(MAXLEN)
surv = []
cnt = 0
for pi in (0, 1):
    for u in W:
        for v in W:
            cnt += 1
            secs = [(shift(u, g), shift(v, g)) for g in range(GENS)]
            pis = [pi] * GENS
            lev, P, Pi = run(pis, secs, rels, LCHK)
            if lev == LCHK:
                oa = order(P[0])
                surv.append((pi, u, v, oa))
names = "abcd"
def fmt(w):
    return "".join(names[g] if e == 1 else names[g].upper() for g, e in w) or "1"
print("n=%d maxlen=%d checked=%d survivors(level %d)=%d" % (n, MAXLEN, cnt, LCHK, len(surv)))
from collections import Counter
print("order of a at level", LCHK, Counter(s[3] for s in surv))
for s in surv:
    if s[3] > 8:
        print("pi=%d a=(%s,%s) ord_a=%d" % (s[0], fmt(s[1]), fmt(s[2]), s[3]))
