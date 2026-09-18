"""Real-vertex cross-check (no abstraction) for the K1 order on SB_3.

For every vertex v != o with sum |x_i| <= R, compute the earlier neighbours of v under
K1 = (sum |x_i|, -sum |h(x_i)|, (|x_1|,|x_2|,|x_3|)) and, inside the subgraph induced on
vertices with strictly smaller key, the largest distance from the first earlier neighbour
to the others (search radius capped at CAP). Key-smaller vertices have sum |x_i| <= sum |x_i(v)|,
so the search space is finite and entirely enumerated.

Usage: python3 sb3_real_vertex_census.py R CAP
"""
import sys
from collections import Counter

R = int(sys.argv[1]) if len(sys.argv) > 1 else 6
CAP = int(sys.argv[2]) if len(sys.argv) > 2 else 8
INV = {"a": "A", "A": "a", "b": "B", "B": "b"}
HT = {"a": 1, "b": 1, "A": -1, "B": -1}


def mul(w, ch):
    return w[:-1] if w and w[-1] == INV[ch] else w + ch


def key(v):
    return (sum(len(x) for x in v), -sum(abs(sum(HT[c] for c in x)) for x in v), tuple(len(x) for x in v))


def nbrs(v):
    for i in range(3):
        for j in range(3):
            if i != j:
                for u in "ab":
                    for d in "AB":
                        w = list(v)
                        w[i] = mul(v[i], u)
                        w[j] = mul(v[j], d)
                        yield tuple(w)


def main():
    o = ("", "", "")
    worst = 0
    hist = Counter()
    bad = 0
    count = 0
    # vertices at sum-length s are reached from sum-length <= s-2 or s, so BFS by layers
    seen = {o}
    layer = [o]
    allv = [o]
    frontier = [o]
    while frontier:
        nf = []
        for v in frontier:
            for y in nbrs(v):
                if y not in seen and key(y)[0] <= R:
                    seen.add(y)
                    nf.append(y)
                    allv.append(y)
        frontier = nf
    for v in allv:
        if v == o:
            continue
        count += 1
        kv = key(v)
        E = sorted({y for y in nbrs(v) if key(y) < kv})
        if not E:
            print("NO EARLIER NEIGHBOUR", v)
            bad += 1
            continue
        todo = set(E[1:])
        dist = {E[0]: 0}
        fr = [E[0]]
        d = 0
        far = 0
        while todo and fr and d < CAP:
            d += 1
            nf = []
            for x in fr:
                for y in nbrs(x):
                    if y not in dist and key(y) < kv:
                        dist[y] = d
                        nf.append(y)
                        if y in todo:
                            todo.discard(y)
                            far = d
            fr = nf
        if todo:
            print("NOT JOINED WITHIN CAP", v, len(E), len(todo))
            bad += 1
            continue
        hist[far] += 1
        worst = max(worst, far)
    print("R", R, "CAP", CAP, "vertices checked", count, "bad", bad, "max depth from first earlier neighbour", worst)
    print("depth histogram", sorted(hist.items()))
    print("DONE")


if __name__ == "__main__":
    main()
