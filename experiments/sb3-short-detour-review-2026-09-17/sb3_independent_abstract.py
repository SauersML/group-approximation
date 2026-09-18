"""Independent re-implementation (referee, 2026-09-17) of the finite configuration census for
sb3-radial-height-order-is-a-short-detour-enumeration.  Written from the statement only, not from
sb3_abstract.py: words are strings over 'abAB', heights of saturated trees are handled by interval
arithmetic, and for every configuration the script computes the least eccentricity (over all choices of
e_0 in E(v)) of E(v) inside the graph of strictly earlier vertices, not just the eccentricity of one e_0.

Model.  SB_3 = ker(F_2^3 -> Z), all generators -> 1, acting on level-0 vertices of T^3.  Generators
x_i y_j^{-1} (i != j, x, y in {a, b}) act by right multiplication: an up letter in tree i and a down
letter in tree j.  Key K1(v) = (sum |x_i|, -sum |h(x_i)|, (|x_1|, |x_2|, |x_3|)), lexicographic.

Abstraction.  A tree with |x| <= ELL is stored exactly.  A tree with |x| > ELL stores its last ELL
letters and the interval of h(x): exact value if |h| < M, [M, inf) or (-inf, -M] otherwise.  Moves that
would touch the unknown prefix are forbidden (so abstract paths are real paths).  A vertex is 'earlier'
only if its key is smaller than v's for EVERY height consistent with the interval.

Usage: python3 sb3_independent_abstract.py ELL M DEPTH NPROC
"""
import itertools
import sys
from multiprocessing import Pool

INV = {'a': 'A', 'A': 'a', 'b': 'B', 'B': 'b'}
UP = 'ab'
DOWN = 'AB'
INF = float('inf')


def height(w):
    return sum(1 if ch in UP else -1 for ch in w)


def reduced_words(n):
    out = ['']
    layer = ['']
    for _ in range(n):
        layer = [w + ch for w in layer for ch in 'abAB' if not (w and INV[ch] == w[-1])]
        out.extend(layer)
    return out


def tree_states(ELL, M):
    states = []
    for w in reduced_words(ELL):
        h = height(w)
        states.append((True, w, (h, h)))
    for w in reduced_words(ELL):
        if len(w) != ELL:
            continue
        for c in range(-M + 1, M):
            states.append((False, w, (c, c)))
        states.append((False, w, (M, INF)))
        states.append((False, w, (-INF, -M)))
    return states


def can_sum_to_zero(cfg):
    lo = sum(s[2][0] for s in cfg)
    hi = sum(s[2][1] for s in cfg)
    return lo <= 0 <= hi


def apply(state_exact, word, ch):
    """Right-multiply a tree coordinate by a letter; None if the move touches the unknown prefix."""
    if word and word[-1] == INV[ch]:
        return word[:-1]
    if not word and not state_exact:
        return None
    return word + ch


def neighbours(cfg, cur):
    out = []
    for i in range(3):
        for j in range(3):
            if i == j:
                continue
            for x in UP:
                a = apply(cfg[i][0], cur[i], x)
                if a is None:
                    continue
                for y in DOWN:
                    b = apply(cfg[j][0], cur[j], y)
                    if b is None:
                        continue
                    w = list(cur)
                    w[i] = a
                    w[j] = b
                    out.append(tuple(w))
    return out


def abs_change_interval(hint, dh):
    """Range of |h + dh| - |h| for h in the interval hint."""
    lo, hi = hint
    if lo == hi:
        v = abs(lo + dh) - abs(lo)
        return (v, v)
    # |h+dh| - |h| is piecewise linear in h; for |h| large it is constant = sign(h)*dh.
    # Evaluate on integer points from the finite end out to where it stabilises.
    if hi == INF:
        pts = range(int(lo), int(lo) + abs(dh) + 2)
    else:
        pts = range(int(hi) - abs(dh) - 1, int(hi) + 1)
    vals = [abs(h + dh) - abs(h) for h in pts]
    return (min(vals), max(vals))


def compare(cfg, cur):
    """True if cur is strictly earlier than v for every consistent height, False if it is never
    earlier, None if it depends on the unknown height."""
    dl = [len(cur[k]) - len(cfg[k][1]) for k in range(3)]
    s = sum(dl)
    if s != 0:
        return s < 0
    lo = hi = 0
    for k in range(3):
        dh = height(cur[k]) - height(cfg[k][1])
        a, b = abs_change_interval(cfg[k][2], dh)
        lo += a
        hi += b
    # earlier iff sum|h| increases (second key component -sum|h| decreases)
    if lo > 0:
        return True
    if hi < 0:
        return False
    if lo == hi == 0:
        for k in range(3):
            if dl[k] != 0:
                return dl[k] < 0
        return False
    return None


def check(args):
    cfg, DEPTH = args
    base = tuple(s[1] for s in cfg)
    E = []
    for w in set(neighbours(cfg, base)):
        c = compare(cfg, w)
        if c is None:
            return ('undetermined-neighbour', cfg, None)
        if c:
            E.append(w)
    if not E:
        return ('no-earlier-neighbour', cfg, None)
    best = None
    for e0 in E:
        dist = {e0: 0}
        frontier = [e0]
        need = set(E) - {e0}
        d = 0
        while need and frontier and d < DEPTH:
            d += 1
            nxt = []
            for x in frontier:
                for y in neighbours(cfg, x):
                    if y not in dist and compare(cfg, y) is True:
                        dist[y] = d
                        nxt.append(y)
                        need.discard(y)
            frontier = nxt
        if not need:
            ecc = max(dist[e] for e in E)
            best = ecc if best is None else min(best, ecc)
            if best <= 2:
                break
    if best is None:
        return ('disconnected-within-depth', cfg, len(E))
    return ('ok', None, best)


if __name__ == '__main__':
    ELL, M, DEPTH, NP = (int(t) for t in sys.argv[1:5])
    TS = tree_states(ELL, M)
    CF = [c for c in itertools.product(TS, TS, TS)
          if can_sum_to_zero(c) and not all(s[0] and s[1] == '' for s in c)]
    print('ELL', ELL, 'M', M, 'DEPTH', DEPTH, 'tree states', len(TS), 'feasible configs', len(CF), flush=True)
    hist = {}
    bad = []
    with Pool(NP) as p:
        for r in p.imap_unordered(check, ((c, DEPTH) for c in CF), chunksize=512):
            if r[0] == 'ok':
                hist[r[2]] = hist.get(r[2], 0) + 1
            else:
                bad.append(r)
    print('min-eccentricity histogram', dict(sorted(hist.items())), flush=True)
    print('bad', len(bad), flush=True)
    for r in bad[:20]:
        print(r)
    print('DONE', flush=True)
