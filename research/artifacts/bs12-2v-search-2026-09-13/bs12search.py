#!/usr/bin/env python3
"""Search small elements g of Brin's 2V for f g f^-1 = g^2 with f a baker map.

Elements are tables of brick pairs ((d1, d2), (r1, r2)) over the alphabet {0,1}:
g(d1 w1, d2 w2) = (r1 w1, r2 w2). Usage:
  bs12search.py selftest
  bs12search.py search NMAX SHARD NSHARDS
"""
import sys, itertools

def contains(big, small):
    return small[0].startswith(big[0]) and small[1].startswith(big[1])

def compatible(a, b):
    return all(x.startswith(y) or y.startswith(x) for x, y in zip(a, b))

def apply_brick(g, beta):
    """Partition brick beta into sub-bricks on which g acts by one table pair."""
    out, stack = [], [beta]
    while stack:
        b = stack.pop()
        done = False
        for d, r in g:
            if contains(d, b):
                img = (r[0] + b[0][len(d[0]):], r[1] + b[1][len(d[1]):])
                out.append((b, img)); done = True; break
        if done:
            continue
        for d, r in g:
            if compatible(d, b):
                i = 0 if len(d[0]) > len(b[0]) else 1
                if len(d[i]) <= len(b[i]):
                    i = 1 - i
                if i == 0:
                    stack.append((b[0] + '0', b[1])); stack.append((b[0] + '1', b[1]))
                else:
                    stack.append((b[0], b[1] + '0')); stack.append((b[0], b[1] + '1'))
                done = True; break
        if not done:
            raise ValueError('brick not covered: %r' % (b,))
    return out

def compose(g, h):
    """Return g o h."""
    out = []
    for d, r in h:
        for sub, img in apply_brick(g, r):
            s0, s1 = sub[0][len(r[0]):], sub[1][len(r[1]):]
            out.append(((d[0] + s0, d[1] + s1), img))
    return tuple(out)

def inverse(g):
    return tuple((r, d) for d, r in g)

def is_identity(g):
    return all(d == r for d, r in g)

def equal(g, h):
    return is_identity(compose(g, inverse(h)))

def power(g, k):
    res = ((('', ''), ('', '')),)
    for _ in range(k):
        res = compose(g, res)
    return res

def decompositions(n, maxdepth):
    """All partitions of the square into exactly n bricks, sides at most maxdepth."""
    seen = set()
    res = []
    def rec(parts):
        key = tuple(sorted(parts))
        if key in seen:
            return
        seen.add(key)
        if len(parts) == n:
            res.append(key); return
        for idx, (a, b) in enumerate(parts):
            rest = parts[:idx] + parts[idx + 1:]
            if len(a) < maxdepth:
                rec(rest + [(a + '0', b), (a + '1', b)])
            if len(b) < maxdepth:
                rec(rest + [(a, b + '0'), (a, b + '1')])
    rec([('', '')])
    return res

BAKERS = {
    'b': (('0', ''), ('', '0')), 'b1': (('1', ''), ('', '1')),
}
def bakers():
    b = ((('0', ''), ('', '0')), (('1', ''), ('', '1')))
    bflip = ((('0', ''), ('', '1')), (('1', ''), ('', '0')))
    return {'b': b, 'binv': inverse(b), 'bflip': bflip, 'bflipinv': inverse(bflip)}

def infinite_order(g, cap=48):
    p = g
    for k in range(1, cap + 1):
        if is_identity(p):
            return False
        p = compose(g, p)
    return True

def selftest():
    b = bakers()['b']
    assert is_identity(compose(b, inverse(b)))
    # f in V acting on the second coordinate: 0 -> 00, 10 -> 01, 11 -> 1
    f = ((('', '0'), ('', '00')), (('', '10'), ('', '01')), (('', '11'), ('', '1')))
    # Kojima--Sheng style root h1(0x,y) = (1x,y), h1(1x,y) = (0x, f y)
    h1 = [(('0', ''), ('1', ''))]
    for d, r in f:
        h1.append((('1', d[1]), ('0', r[1])))
    h1 = tuple(h1)
    idf = f
    assert equal(compose(h1, h1), idf), 'h1^2 != id x f'
    assert infinite_order(f)
    # disjoint supports commute
    s = ((('0', ''), ('0', '')), (('10', ''), ('11', '')), (('11', ''), ('10', '')))
    t = ((('1', ''), ('1', '')), (('00', ''), ('01', '')), (('01', ''), ('00', '')))
    assert equal(compose(s, t), compose(t, s))
    print('selftest OK')

def search(nmax, shard, nshards, maxdepth=3):
    fs = bakers()
    decs = {n: decompositions(n, maxdepth) for n in range(1, nmax + 1)}
    count = found = 0
    idx = 0
    for n in range(1, nmax + 1):
        for D in decs[n]:
            for R in decs[n]:
                for perm in itertools.permutations(range(n)):
                    idx += 1
                    if idx % nshards != shard:
                        continue
                    g = tuple((D[i], R[perm[i]]) for i in range(n))
                    if is_identity(g):
                        continue
                    count += 1
                    g2 = compose(g, g)
                    for name, f in fs.items():
                        if equal(compose(compose(f, g), inverse(f)), g2) and infinite_order(g):
                            found += 1
                            print('WITNESS', name, g, flush=True)
    print('DONE shard=%d/%d nmax=%d maxdepth=%d elements=%d witnesses=%d' % (shard, nshards, nmax, maxdepth, count, found), flush=True)

if __name__ == '__main__':
    if sys.argv[1] == 'selftest':
        selftest()
    else:
        search(int(sys.argv[2]), int(sys.argv[3]), int(sys.argv[4]), int(sys.argv[5]) if len(sys.argv) > 5 else 3)
