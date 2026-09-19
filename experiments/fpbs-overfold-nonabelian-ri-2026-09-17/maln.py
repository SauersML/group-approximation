"""Malnormality test (Kapovich-Myasnikov): <G> is malnormal in F iff every
component of core(G) x core(G) off the diagonal is a tree."""
from stall import INV


def malnormal(G):
    adj, _ = G
    seen = set()
    for s in ((p, q) for p in adj for q in adj if p != q):
        if s in seen:
            continue
        comp = [s]
        seen.add(s)
        e2 = 0
        for (p, q) in comp:
            for x, p2 in adj[p].items():
                if x in adj[q]:
                    e2 += 1
                    t = (p2, adj[q][x])
                    if t not in seen:
                        seen.add(t)
                        comp.append(t)
        if any(p == q for (p, q) in comp):
            continue  # diagonal component (cannot happen off-diagonal)
        if e2 // 2 - len(comp) + 1 > 0:
            return False
    return True
