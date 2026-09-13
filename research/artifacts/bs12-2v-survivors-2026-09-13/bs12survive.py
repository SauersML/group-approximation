#!/usr/bin/env python3
"""Classify small elements g of Brin's 2V against necessary conditions for being
the infinite-order generator s of a copy of BS(1,2) (f s f^-1 = s^2, any f).

For p = 1, 2, ..., P the table of g^p is inspected:
  torsion   g^p = id, so g has finite order;
  hyp       some brick (u -> v) of g^p has u_j, v_j prefix-comparable in every
            coordinate and |u_j| != |v_j| in some coordinate: g^p has a fixed
            point there with nonzero exponent. Item 2 of
            bs-kl-images-in-brin-thompson-groups-have-open-periodic-sets
            excludes g for every conjugator f;
  blowup    the table of g^p exceeds CAP bricks (undecided);
  survivor  none of the above for p <= P.
Usage:
  bs12survive.py selftest
  bs12survive.py run NMAX SHARD NSHARDS [MAXDEPTH]
"""
import sys, itertools, hashlib
sys.path.insert(0, __file__.rsplit('/', 1)[0])
from bs12search import compose, is_identity, decompositions, bakers, inverse

P, CAP = 48, 4000

def comparable(a, b):
    return a.startswith(b) or b.startswith(a)

def hyperbolic_fixed_brick(gp):
    for d, r in gp:
        if all(comparable(x, y) for x, y in zip(d, r)) and \
           any(len(x) != len(y) for x, y in zip(d, r)):
            return (d, r)
    return None

def classify(g):
    p = g
    for k in range(1, P + 1):
        if is_identity(p):
            return 'torsion', k
        if hyperbolic_fixed_brick(p) is not None:
            return 'hyp', k
        if len(p) > CAP:
            return 'blowup', k
        p = compose(g, p)
    return 'survivor', P

def depth(g):
    return max(max(len(x) for x in d + r) for d, r in g)

def depth_profile(g, kmax=6):
    out, p = [], g
    for k in range(kmax + 1):
        out.append(depth(p))
        if len(p) > CAP:
            out.append('cap'); break
        p = compose(p, p)
    return out

def selftest():
    b = bakers()['b']
    assert classify(b) == ('hyp', 1), classify(b)
    f = ((('', '0'), ('', '00')), (('', '10'), ('', '01')), (('', '11'), ('', '1')))
    assert classify(f) == ('hyp', 1), classify(f)
    h1 = [(('0', ''), ('1', ''))] + [(('1', d[1]), ('0', r[1])) for d, r in f]
    assert classify(tuple(h1)) == ('hyp', 2), classify(tuple(h1))
    s = ((('0', ''), ('0', '')), (('10', ''), ('11', '')), (('11', ''), ('10', '')))
    assert classify(s) == ('torsion', 2), classify(s)
    c3 = ((('00', ''), ('01', '')), (('01', ''), ('1', '')), (('1', ''), ('00', '')))
    assert classify(c3) == ('torsion', 3), classify(c3)
    # a 64-cycle of depth-6 cubes has order 64 > P and zero exponents: survivor
    ws = [format(i, '06b') for i in range(64)]
    c64 = tuple(((ws[i], ''), (ws[(i + 1) % 64], '')) for i in range(64))
    assert classify(c64) == ('survivor', P), classify(c64)
    print('selftest OK')

def run(nmax, shard, nshards, maxdepth=3):
    decs = {n: decompositions(n, maxdepth) for n in range(1, nmax + 1)}
    counts = {'torsion': 0, 'hyp': 0, 'blowup': 0, 'survivor': 0}
    idx = shown = 0
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
                    cls, k = classify(g)
                    counts[cls] += 1
                    if cls == 'survivor' or (cls == 'blowup' and shown < 40):
                        shown += cls == 'blowup'
                        print(cls.upper(), k, g, depth_profile(g), flush=True)
    print('DONE shard=%d/%d nmax=%d maxdepth=%d P=%d CAP=%d %s' % (
        shard, nshards, nmax, maxdepth, P, CAP,
        ' '.join('%s=%d' % kv for kv in sorted(counts.items()))), flush=True)

if __name__ == '__main__':
    me = open(__file__, 'rb').read()
    dep = open(__file__.rsplit('/', 1)[0] + '/bs12search.py', 'rb').read()
    print('md5 bs12survive.py', hashlib.md5(me).hexdigest(),
          'bs12search.py', hashlib.md5(dep).hexdigest(), flush=True)
    if sys.argv[1] == 'selftest':
        selftest()
    else:
        run(int(sys.argv[2]), int(sys.argv[3]), int(sys.argv[4]),
            int(sys.argv[5]) if len(sys.argv) > 5 else 3)
