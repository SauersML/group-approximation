# Small perfect groups as multiplication tables (permutation groups), for hom screening.
import itertools
def closure(gens, n):
    idt = tuple(range(n)); els = {idt}; frontier = [idt]
    while frontier:
        nf = []
        for a in frontier:
            for g in gens:
                b = tuple(g[a[k]] for k in range(n))
                if b not in els: els.add(b); nf.append(b)
        frontier = nf
    return sorted(els)
def table(els):
    n = len(els[0]); idx = {p: i for i, p in enumerate(els)}
    mul = [[idx[tuple(a[b[k]] for k in range(n))] for b in els] for a in els]  # a o b (apply b first)
    inv = [idx[tuple(sorted(range(n), key=lambda k: a[k]))] for a in els]
    return mul, inv, idx[tuple(range(n))]
def psl2(p):
    # PSL(2,p) acting on the projective line {0..p-1, inf=p}
    def mob(a, b, c, d):
        out = []
        for z in range(p + 1):
            if z == p: num, den = a, c
            else: num, den = (a * z + b) % p, (c * z + d) % p
            out.append(p if den == 0 else num * pow(den, -1, p) % p)
        return tuple(out)
    return closure([mob(1, 1, 0, 1), mob(0, p - 1, 1, 0)], p + 1)
def alt(n):
    g1 = tuple([1, 2, 0] + list(range(3, n)))
    g2 = tuple(list(range(1, n)) + [0]) if n % 2 == 1 else tuple([0] + list(range(2, n)) + [1])
    return closure([g1, g2], n)
def psl28():
    # PSL(2,8) on 9 points: F_8 = F_2[a]/(a^3+a+1), elements 0..7 as bit vectors, inf = 8
    def m(a, b):
        r = 0
        for i in range(3):
            if b >> i & 1: r ^= a << i
        for i in (4, 3):
            if r >> i & 1: r ^= 0b1011 << (i - 3)
        return r
    invs = {x: next(y for y in range(1, 8) if m(x, y) == 1) for x in range(1, 8)}
    def mob(a, b, c, d):
        out = []
        for z in range(9):
            if z == 8: num, den = a, c
            else: num, den = m(a, z) ^ b, m(c, z) ^ d
            out.append(8 if den == 0 else m(num, invs[den]))
        return tuple(out)
    return closure([mob(1, 1, 0, 1), mob(2, 0, 0, invs[2]), mob(0, 1, 1, 0)], 9)
GROUPS = {'A5': lambda: alt(5), 'PSL27': lambda: psl2(7), 'A6': lambda: alt(6),
          'PSL28': psl28, 'PSL211': lambda: psl2(11), 'PSL213': lambda: psl2(13), 'A7': lambda: alt(7)}
def get(name):
    els = GROUPS[name](); mul, inv, e = table(els)
    reps, seen = [], set()
    for a in range(len(els)):
        if a in seen: continue
        reps.append(a)
        for b in range(len(els)): seen.add(mul[mul[b][a]][inv[b]])
    return len(els), mul, inv, e, reps
if __name__ == '__main__':
    for k in GROUPS:
        if k == 'A7': continue
        n, mul, inv, e, reps = get(k); print(k, n, len(reps))
