"""Referee cross-check (2026-09-17): real-vertex census for the K1 order on SB_3, independent of the
abstraction.  For each level-0 vertex v != o of T^3 it computes E(v) = neighbours of strictly smaller key
and the least eccentricity of E(v) (over e_0 in E(v)) in the graph of strictly earlier vertices, with a
depth cap.  Reports the histogram and any failure.

Usage:
  python3 sb3_real_vertex_census.py exhaustive MAXLEN NPROC
  python3 sb3_real_vertex_census.py random MAXLEN COUNT SEED NPROC   (biased towards large |heights|)
"""
import itertools
import random
import sys
from multiprocessing import Pool

INV = {'a': 'A', 'A': 'a', 'b': 'B', 'B': 'b'}
CAP = 8


def h(w):
    return sum(1 if c in 'ab' else -1 for c in w)


def mul(w, c):
    return w[:-1] if w and w[-1] == INV[c] else w + c


def key(v):
    return (sum(len(x) for x in v), -sum(abs(h(x)) for x in v), tuple(len(x) for x in v))


def nbrs(v):
    for i in range(3):
        for j in range(3):
            if i != j:
                for x in 'ab':
                    for y in 'AB':
                        w = list(v)
                        w[i] = mul(w[i], x)
                        w[j] = mul(w[j], y)
                        yield tuple(w)


def check(v):
    kv = key(v)
    E = [w for w in set(nbrs(v)) if key(w) < kv]
    if not E:
        return ('no-earlier-neighbour', v)
    best = None
    for e0 in E:
        dist = {e0: 0}
        fr = [e0]
        need = set(E) - {e0}
        d = 0
        while need and fr and d < CAP:
            d += 1
            nf = []
            for x in fr:
                for y in nbrs(x):
                    if y not in dist and key(y) < kv:
                        dist[y] = d
                        nf.append(y)
                        need.discard(y)
            fr = nf
        if not need:
            ecc = max(dist[e] for e in E)
            best = ecc if best is None else min(best, ecc)
            if best <= 2:
                break
    if best is None:
        return ('disconnected-within-cap', v)
    return ('ok', best)


def words(n):
    out = ['']
    layer = ['']
    for _ in range(n):
        layer = [w + c for w in layer for c in 'abAB' if not (w and INV[c] == w[-1])]
        out.extend(layer)
    return out


def rand_word(rng, n):
    bias = rng.choice([0.5, 0.8, 0.2, 0.95, 0.05])
    w = ''
    while len(w) < n:
        c = rng.choice('ab') if rng.random() < bias else rng.choice('AB')
        if not (w and INV[c] == w[-1]):
            w += c
    return w


def run(vs, NP):
    hist = {}
    bad = []
    with Pool(NP) as p:
        for r in p.imap_unordered(check, vs, chunksize=64):
            if r[0] == 'ok':
                hist[r[1]] = hist.get(r[1], 0) + 1
            else:
                bad.append(r)
    print('vertices', len(vs), 'min-eccentricity histogram', dict(sorted(hist.items())), 'bad', len(bad), flush=True)
    for r in bad[:20]:
        print(r)
    print('DONE', flush=True)


if __name__ == '__main__':
    mode = sys.argv[1]
    if mode == 'exhaustive':
        n, NP = int(sys.argv[2]), int(sys.argv[3])
        W = words(n)
        vs = [v for v in itertools.product(W, W, W) if sum(h(x) for x in v) == 0 and v != ('', '', '')]
        run(vs, NP)
    else:
        n, cnt, seed, NP = (int(t) for t in sys.argv[2:6])
        rng = random.Random(seed)
        vs = []
        while len(vs) < cnt:
            a = rand_word(rng, rng.randint(0, n))
            b = rand_word(rng, rng.randint(0, n))
            # choose the third word to balance the height exactly, when possible
            need = -(h(a) + h(b))
            L = rng.randint(abs(need), max(abs(need), n))
            if (L - abs(need)) % 2:
                L += 1
            k = (L + need) // 2  # number of up letters
            letters = ['u'] * k + ['d'] * (L - k)
            rng.shuffle(letters)
            c = ''
            for t in letters:
                opts = [x for x in ('ab' if t == 'u' else 'AB') if not (c and INV[x] == c[-1])]
                c += rng.choice(opts)
            v = tuple(rng.sample([a, b, c], 3))
            if sum(h(x) for x in v) == 0 and v != ('', '', ''):
                vs.append(v)
        run(vs, NP)
