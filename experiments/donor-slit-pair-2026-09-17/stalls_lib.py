from swap import *
def components(b, c):
    uf = UF(len(b))
    for x in range(len(b)): uf.u(x, b[x]); uf.u(x, c[x])
    comps = {}
    for x in range(len(b)): comps.setdefault(uf.f(x), []).append(x)
    return list(comps.values())
def restrict(b, c, cm):
    idx = {x: i for i, x in enumerate(cm)}
    return [idx[b[x]] for x in cm], [idx[c[x]] for x in cm]
def cylinders(b, c):
    """horizontal cylinders of (b right, c up): rows = b-cycles; row R continues to c(R) as the same cylinder iff
    c maps R onto a single row and commutes with b there. Returns sorted list of (circumference, height)."""
    d = len(b); rowid = [-1]*d; rows = []
    for x in range(d):
        if rowid[x] < 0:
            r = []; y = x
            while rowid[y] < 0: rowid[y] = len(rows); r.append(y); y = b[y]
            rows.append(r)
    nxt = {}
    for i, r in enumerate(rows):
        ok = all(c[b[y]] == b[c[y]] for y in r) and len({rowid[c[y]] for y in r}) == 1
        if ok: nxt[i] = rowid[c[r[0]]]
    prev = {j: i for i, j in nxt.items()}
    seen = set(); out = []
    for i in range(len(rows)):
        if i in seen: continue
        # go down to the start of the cylinder
        j = i; steps = 0
        while j in prev and prev[j] != i and steps < len(rows):
            j = prev[j]; steps += 1
            if j == i: break
        start = j; h = 0; k = start
        while True:
            seen.add(k); h += 1
            if k in nxt and nxt[k] != start and nxt[k] not in seen: k = nxt[k]
            else: break
        out.append((len(rows[start]), h))
    return sorted(out)
