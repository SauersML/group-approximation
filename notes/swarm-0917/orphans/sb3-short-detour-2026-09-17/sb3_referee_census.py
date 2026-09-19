"""Independent referee census for sb3-radial-height-order-is-a-short-detour-enumeration.

Written from scratch (2026-09-17, swarm-0917-w5-pull-z-2); it does not import or copy
research/artifacts/zp-sb3-short-detour-2026-09-13-part4.md's script.

Model. SB_3 = {(x1,x2,x3) in F(a,b)^3 : h(x1)+h(x2)+h(x3) = 0}, h(a)=h(b)=+1, h(A)=h(B)=-1.
Generators: right-multiply one coordinate i by an up letter and another j != i by a down
letter (24 generators, closed under inverses). Key K1(v) = (sum |x_i|, -sum |h(x_i)|, (|x_1|,|x_2|,|x_3|)).

Abstraction of one coordinate ("tree state"):
  ('E', w, h)   the whole reduced word w is known, |w| <= ELL, h = h(w);
  ('T', w, c)   |x| > ELL, w = last ELL letters, c = h(x) clipped to [-M, M]
                (c = +M means h >= M, c = -M means h <= -M).
Every vertex v != o lies in some feasible configuration (triple of tree states).

For each configuration we:
  1. list the abstract neighbours of the base (moves only touch known letters);
  2. decide for each neighbour whether its key is smaller than the base key; if any
     decision depends on the unknown part of a height, the configuration FAILS;
  3. BFS inside the set of abstract states whose key is *certainly* smaller than the base,
     from the first earlier neighbour, up to depth DEPTH, and record the depth at which
     all earlier neighbours have been reached (FAIL if not reached).
Output: counts, depth histogram, failures.

Usage: python3 sb3_referee_census.py ELL M DEPTH NPROC [pairwise]
With 'pairwise', step 3 is run from every earlier neighbour and the histogram records the
largest distance between two earlier neighbours (so DEPTH is then a bound on L itself).
"""
import itertools
import sys
from collections import Counter
from multiprocessing import Pool

ELL = int(sys.argv[1]) if len(sys.argv) > 1 else 2
M = int(sys.argv[2]) if len(sys.argv) > 2 else 3
DEPTH = int(sys.argv[3]) if len(sys.argv) > 3 else 6
NPROC = int(sys.argv[4]) if len(sys.argv) > 4 else 4
PAIRWISE = len(sys.argv) > 5 and sys.argv[5] == "pairwise"

UP = "ab"
DOWN = "AB"
INV = {"a": "A", "A": "a", "b": "B", "B": "b"}
HT = {"a": 1, "b": 1, "A": -1, "B": -1}


def height(w):
    return sum(HT[ch] for ch in w)


def reduced_words(n):
    """All reduced words of length exactly n."""
    if n == 0:
        return [""]
    out = []
    for w in reduced_words(n - 1):
        for ch in "abAB":
            if not w or w[-1] != INV[ch]:
                out.append(w + ch)
    return out


def tree_states():
    out = []
    for n in range(ELL + 1):
        for w in reduced_words(n):
            out.append(("E", w, height(w)))
    for w in reduced_words(ELL):
        for c in range(-M, M + 1):
            out.append(("T", w, c))
    return out


def height_interval(st):
    kind, w, c = st
    if kind == "E" or abs(c) < M:
        return (c, c)
    if c == M:
        return (M, None)  # None = +infinity
    return (None, -M)  # None = -infinity


def feasible(cfg):
    if all(st[0] == "E" and st[1] == "" for st in cfg):
        return False  # the base vertex o itself
    lo_inf = hi_inf = False
    lo = hi = 0
    for st in cfg:
        a, b = height_interval(st)
        if a is None:
            lo_inf = True
        else:
            lo += a
        if b is None:
            hi_inf = True
        else:
            hi += b
    return (lo_inf or lo <= 0) and (hi_inf or hi >= 0)


def move(st, w, ch):
    """Right-multiply the abstract coordinate whose current known part is w by letter ch."""
    if w and w[-1] == INV[ch]:
        return w[:-1]
    if st[0] == "T" and w == "":
        return None  # would touch the unknown prefix
    return w + ch


def neighbours(cfg, cur):
    for i in range(3):
        for j in range(3):
            if i == j:
                continue
            for u in UP:
                wi = move(cfg[i], cur[i], u)
                if wi is None:
                    continue
                for d in DOWN:
                    wj = move(cfg[j], cur[j], d)
                    if wj is None:
                        continue
                    nxt = list(cur)
                    nxt[i] = wi
                    nxt[j] = wj
                    yield tuple(nxt)


def abs_height_change(st, dh):
    """Exact change of |h| when h moves by dh, or None if it depends on unknown data."""
    kind, w, c = st
    if kind == "E" or abs(c) < M:
        return abs(c + dh) - abs(c)
    if c == M:  # h >= M
        return dh if dh >= -M else None
    return -dh if dh <= M else None  # h <= -M


def compare(cfg, cur):
    """True if key(cur) < key(base) for every vertex in the configuration, False if key(cur) >= key(base)
    for every such vertex, None if undetermined."""
    base = [st[1] for st in cfg]
    dl = [len(cur[k]) - len(base[k]) for k in range(3)]
    if sum(dl) != 0:
        return sum(dl) < 0
    dhs = 0
    for k in range(3):
        ch = abs_height_change(cfg[k], height(cur[k]) - height(base[k]))
        if ch is None:
            return None
        dhs += ch
    if dhs != 0:
        return dhs > 0  # more height spread = smaller key
    for k in range(3):
        if dl[k] != 0:
            return dl[k] < 0
    return False  # equal key: not certainly earlier


def check(cfg):
    base = tuple(st[1] for st in cfg)
    earlier = []
    for nb in set(neighbours(cfg, base)):
        r = compare(cfg, nb)
        if r is None:
            return ("undetermined-neighbour", cfg)
        if r:
            earlier.append(nb)
    if not earlier:
        return ("no-earlier-neighbour", cfg)
    earlier.sort()
    src = earlier[0]
    todo = set(earlier[1:])
    seen = {src}
    frontier = [src]
    depth = 0
    while todo:
        if depth == DEPTH or not frontier:
            return ("disconnected", cfg, len(earlier), len(todo))
        depth += 1
        nf = []
        for x in frontier:
            for y in neighbours(cfg, x):
                if y in seen:
                    continue
                if compare(cfg, y) is True:
                    seen.add(y)
                    nf.append(y)
                    todo.discard(y)
        frontier = nf
    return ("ok", depth, len(earlier))


def check_pairwise(cfg):
    """Largest distance, inside the certainly-earlier abstract states, between two earlier
    neighbours (each BFS capped at DEPTH). Used with DEPTH = 10 to certify L = 10 directly."""
    base = tuple(st[1] for st in cfg)
    earlier = []
    for nb in set(neighbours(cfg, base)):
        r = compare(cfg, nb)
        if r is None:
            return ("undetermined-neighbour", cfg)
        if r:
            earlier.append(nb)
    if not earlier:
        return ("no-earlier-neighbour", cfg)
    earlier.sort()
    worst = 0
    for a_idx in range(len(earlier) - 1):
        src = earlier[a_idx]
        todo = set(earlier[a_idx + 1:])
        seen = {src}
        frontier = [src]
        depth = 0
        while todo:
            if depth == DEPTH or not frontier:
                return ("disconnected", cfg, len(earlier), len(todo))
            depth += 1
            nf = []
            for x in frontier:
                for y in neighbours(cfg, x):
                    if y in seen:
                        continue
                    if compare(cfg, y) is True:
                        seen.add(y)
                        nf.append(y)
                        todo.discard(y)
            frontier = nf
        worst = max(worst, depth)
    return ("ok", worst, len(earlier))


def main():
    ts = tree_states()
    cfgs = [c for c in itertools.product(ts, repeat=3) if feasible(c)]
    print("ELL", ELL, "M", M, "DEPTH", DEPTH, "PAIRWISE", PAIRWISE, "tree states", len(ts), "feasible configurations", len(cfgs), flush=True)
    with Pool(NPROC) as pool:
        res = pool.map(check_pairwise if PAIRWISE else check, cfgs, chunksize=512)
    depth_hist = Counter()
    ne_hist = Counter()
    fails = [r for r in res if r[0] != "ok"]
    for r in res:
        if r[0] == "ok":
            depth_hist[r[1]] += 1
            ne_hist[r[2]] += 1
    print("failures", len(fails), Counter(r[0] for r in fails), flush=True)
    for r in fails[:20]:
        print("FAIL", r)
    print("BFS depth histogram", sorted(depth_hist.items()))
    print("number-of-earlier-neighbours histogram", sorted(ne_hist.items()))
    print("DONE", flush=True)


if __name__ == "__main__":
    main()
