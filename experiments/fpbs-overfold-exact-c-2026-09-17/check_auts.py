"""Check an exported instance for deep.c (usage: check_auts.py inst ...).

For each automorphism in the file:
- it is a bijection of Gamma_{j+1}(Q) that preserves every labelled edge;
- it maps m-fibres bijectively to m-fibres, so it preserves ker(m);
- it maps fibres over Q to fibres over Q, so it preserves same-fibre pairs.
These are the facts the automorphism reduction in deep.c relies on."""
import sys


def check(path):
    it = iter(open(path).read().split())
    V, n = int(next(it)), int(next(it))
    nb = [[int(next(it)) for _ in range(4)] for _ in range(V)]
    m = [int(next(it)) for _ in range(V)]
    over = [int(next(it)) for _ in range(V)]
    S = int(next(it))
    for _ in range(3 * S):
        next(it)
    NA = int(next(it))
    auts = [[int(next(it)) for _ in range(V)] for _ in range(NA)]
    ok = True
    for a in auts:
        ok = ok and sorted(a) == list(range(V))
        for v in range(V):
            for k in range(4):
                w, w2 = nb[v][k], nb[a[v]][k]
                ok = ok and (w < 0) == (w2 < 0) and (w < 0 or a[w] == w2)
        for lab in (m, over):
            img = {}
            for v in range(V):
                ok = ok and img.setdefault(lab[v], lab[a[v]]) == lab[a[v]]
            ok = ok and len(set(img.values())) == len(img)
    print(path, 'V', V, 'auts', NA, 'all valid' if ok else 'INVALID')


for p in sys.argv[1:]:
    check(p)
