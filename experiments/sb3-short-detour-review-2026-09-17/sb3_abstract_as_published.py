import itertools, sys
from multiprocessing import Pool
ELL = int(sys.argv[1]); M = int(sys.argv[2]); DEPTH = int(sys.argv[3]); NP = int(sys.argv[4])
def h(x):
    return sum(1 if s > 0 else -1 for s in x)
def words_upto(n):
    out = [()]; fr = [()]
    for _ in range(n):
        fr = [w + (s,) for w in fr for s in (1, 2, -1, -2) if not (w and w[-1] == -s)]; out += fr
    return out
def tree_configs():
    out = []
    for w in words_upto(ELL):
        out.append(('S', w, h(w)))
    for w in words_upto(ELL):
        if len(w) == ELL:
            for c in range(-M, M + 1):
                out.append(('L', w, c))
    return out
def feasible(cfg):
    if all(t[0] == 'S' and len(t[1]) == 0 for t in cfg):
        return False
    lo = 0; hi = 0; unb_lo = False; unb_hi = False
    for kind, w, c in cfg:
        if kind == 'S' or abs(c) < M:
            lo += c; hi += c
        elif c == M:
            lo += M; unb_hi = True; hi += M
        else:
            hi += -M; unb_lo = True; lo += -M
    return (lo <= 0 or unb_lo) and (hi >= 0 or unb_hi)
def step(kind, w, s):
    if w and w[-1] == -s:
        return w[:-1]
    if not w and kind == 'L':
        return None
    return w + (s,)
def nbrs(cfg, cur):
    for i in range(3):
        for j in range(3):
            if i != j:
                for s in (1, 2):
                    for t in (-1, -2):
                        a = step(cfg[i][0], cur[i], s)
                        if a is None:
                            continue
                        b = step(cfg[j][0], cur[j], t)
                        if b is None:
                            continue
                        w = list(cur); w[i] = a; w[j] = b
                        yield tuple(w)
def earlier(cfg, cur):
    dlen = [len(cur[k]) - len(cfg[k][1]) for k in range(3)]
    s = sum(dlen)
    if s < 0:
        return True
    if s > 0:
        return False
    dhs = 0
    for k in range(3):
        kind, w, c = cfg[k]
        dh = h(cur[k]) - h(w)
        if kind == 'S' or abs(c) < M:
            dhs += abs(c + dh) - abs(c)
        elif c == M:
            if dh < -M:
                return None
            dhs += dh
        else:
            if dh > M:
                return None
            dhs += -dh
    if dhs > 0:
        return True
    if dhs < 0:
        return False
    for k in range(3):
        if dlen[k] != 0:
            return dlen[k] < 0
    return False
def check(cfg):
    base = tuple(t[1] for t in cfg)
    E = []
    for w in set(nbrs(cfg, base)):
        e = earlier(cfg, w)
        if e is None:
            return ('undetermined-neighbour', cfg)
        if e:
            E.append(w)
    if not E:
        return ('nolower', cfg)
    seen = {E[0]}; fr = [E[0]]; need = set(E); need.discard(E[0]); D = 0
    while need and D < DEPTH and fr:
        D += 1; nf = []
        for x in fr:
            for y in nbrs(cfg, x):
                if y not in seen and earlier(cfg, y) is True:
                    seen.add(y); nf.append(y); need.discard(y)
        fr = nf
    if need:
        return ('disc', cfg, len(E), len(need))
    return None
if __name__ == '__main__':
    TC = tree_configs()
    CF = [c for c in itertools.product(TC, TC, TC) if feasible(c)]
    with Pool(NP) as p:
        res = p.map(check, CF, chunksize=256)
    bad = [r for r in res if r]
    kinds = {}
    for r in bad:
        kinds[r[0]] = kinds.get(r[0], 0) + 1
    print('ELL', ELL, 'M', M, 'DEPTH', DEPTH, 'tree configs', len(TC), 'feasible configs', len(CF), 'bad', len(bad), kinds, flush=True)
    for r in bad[:15]:
        print(r)
    print('DONE', flush=True)
