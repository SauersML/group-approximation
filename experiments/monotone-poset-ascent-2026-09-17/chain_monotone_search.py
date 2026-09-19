"""Search monotone injective cellular automata over Z on a chain alphabet [k].

A rule f : [k]^w -> [k] (window of w consecutive cells) is monotone if it is
nondecreasing in every coordinate for the chain order 0 < 1 < ... < k-1.
Injectivity over Z is tested with the pair graph on (w-1)-words: the automaton
is non-injective iff some off-diagonal pair vertex lies on a bi-infinite path.

Usage: python3 chain_monotone_search.py k w
Prints the number of monotone rules, the number of injective ones, and every
injective one that is not a copy of one coordinate.
"""
import itertools
import sys

sys.setrecursionlimit(100000)
k = int(sys.argv[1]) if len(sys.argv) > 1 else 3
w = int(sys.argv[2]) if len(sys.argv) > 2 else 2
pts = list(itertools.product(range(k), repeat=w))
order = sorted(pts, key=sum)
preds = {p: [q for q in pts if q != p and all(a <= b for a, b in zip(q, p))] for p in pts}


def gen():
    f = {}

    def bt(i):
        if i == len(order):
            yield dict(f)
            return
        p = order[i]
        lo = max([f[q] for q in preds[p]], default=0)
        for v in range(lo, k):
            f[p] = v
            yield from bt(i + 1)
        del f[p]

    yield from bt(0)


def injective(f):
    words = list(itertools.product(range(k), repeat=w - 1))
    V = [(u, v) for u in words for v in words]
    adj = {x: [] for x in V}
    for u in words:
        for v in words:
            for a in range(k):
                for b in range(k):
                    U = u + (a,)
                    W = v + (b,)
                    if f[U] == f[W]:
                        adj[(u, v)].append((U[1:], W[1:]))
    index, low, st, on, comps, c = {}, {}, [], set(), [], [0]

    def sc(v):
        index[v] = low[v] = c[0]
        c[0] += 1
        st.append(v)
        on.add(v)
        for x in adj[v]:
            if x not in index:
                sc(x)
                low[v] = min(low[v], low[x])
            elif x in on:
                low[v] = min(low[v], index[x])
        if low[v] == index[v]:
            comp = []
            while True:
                x = st.pop()
                on.discard(x)
                comp.append(x)
                if x == v:
                    break
            comps.append(comp)

    for v in V:
        if v not in index:
            sc(v)
    cyc = set()
    for comp in comps:
        if len(comp) > 1 or comp[0] in adj[comp[0]]:
            cyc.update(comp)
    fw = set(cyc)
    q = list(cyc)
    while q:
        v = q.pop()
        for x in adj[v]:
            if x not in fw:
                fw.add(x)
                q.append(x)
    radj = {x: [] for x in V}
    for v in V:
        for x in adj[v]:
            radj[x].append(v)
    bw = set(cyc)
    q = list(cyc)
    while q:
        v = q.pop()
        for x in radj[v]:
            if x not in bw:
                bw.add(x)
                q.append(x)
    return all(v[0] == v[1] for v in fw & bw)


def main():
    cnt = 0
    inj = []
    for f in gen():
        cnt += 1
        if injective(f):
            copy = [t for t in range(w) if all(f[p] == p[t] for p in pts)]
            inj.append((copy, tuple(f[p] for p in pts)))
    print("k", k, "window", w, "monotone rules", cnt, "injective", len(inj))
    noncopy = [t for c, t in inj if not c]
    print("copies", len(inj) - len(noncopy), "non-copies", len(noncopy))
    for t in noncopy[:20]:
        print("NONCOPY", t)


if __name__ == "__main__":
    main()
