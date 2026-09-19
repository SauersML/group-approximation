# Census of degree-one two-cell configurations (fiber-product construction) with ab != 0:
# for each folded graph on n vertices (rank >= minrank), each off-diagonal component Delta of
# Gamma x Gamma, each lam in LAMS and each nullspace vector h of p2 - lam p1 on H_1(Delta), build words
# w = gamma(h) * tail (tail in [pi_1 Delta, pi_1 Delta]), freely and cyclically reduced.  Keep w if it is
# not a proper power and z0 = [w at v0] is a times a primitive vector, a = denominator of lam (degree one).
# Then test the abelianized cylinder row c^ab:
#   'char' : killed by a character into F_q^* (q <= 13)       [exact certificate of non-admissibility]
#   'Qbar' : entries have a common zero over Qbar (ideal over Q[s^+-,t^+-] is proper)
#   'UNIT' : entries generate the unit ideal over Q (only finitely many primes can still kill c)
# usage: python3 census.py n minrank [ntails] [seed]
import sys, random, math
from fractions import Fraction as Fr
from fc import *

LAMS = [Fr(2), Fr(3, 2), Fr(4, 3)]


def tails(gens, k, rng):
    out = [[]]
    m = len(gens)
    for i in range(m):
        for j in range(i + 1, m):
            out.append(gens[i] + gens[j] + inv(gens[i]) + inv(gens[j]))
    rng.shuffle(out[1:])
    out = out[:k]
    for _ in range(k - len(out)):
        i, j = rng.sample(range(m), 2)
        a = gens[i] if rng.random() < .5 else inv(gens[i]); b = gens[j] if rng.random() < .5 else inv(gens[j])
        out.append(a + b + inv(a) + inv(b))
    return out


def rword(tr, root, gens, h, rng, ncomm=1):
    """A random loop in Delta with homology class h: shuffle the factors gamma_k^{+-1} of gamma(h),
    then append ncomm commutators of random products of generators."""
    fac = []
    for k, hk in enumerate(h):
        fac += [gens[k] if hk > 0 else inv(gens[k])] * abs(hk)
    rng.shuffle(fac)
    w = [l for f in fac for l in f]
    def rl():
        u = []
        for _ in range(rng.randint(1, 3)):
            g = rng.choice(gens); u += g if rng.random() < .5 else inv(g)
        return red(u)
    for _ in range(ncomm):
        u, v = rl(), rl(); w += u + v + inv(u) + inv(v)
    return build(tr, root, gens, [0] * len(gens), w)


def run(n, minrank, ntails=3, seed=1, verbose=True, mode='tail'):
    rng = random.Random(seed)
    res = {}; units = []
    for edges in graphs(n, minrank):
        NE = len(edges); tr = mk(edges); rk = NE - n + 1
        for root, par, gens in comps(n, tr):
            if len(gens) < 2: continue
            Z = []
            for gw in gens:
                Z.append((read(tr, root[0], gw, NE)[1], read(tr, root[1], gw, NE)[1]))
            for lam in LAMS:
                for h in nullvecs(Z, NE, lam):
                    for it in range(ntails):
                        if mode == 'tail':
                            tl = tails(gens, ntails, rng)
                            if it >= len(tl): break
                            a, b, w = build(tr, root, gens, h, tl[it])
                        else:
                            a, b, w = rword(tr, root, gens, h, rng, 1 + it % 2)
                        if len(w) < 4 or pp(w): continue
                        z0 = read(tr, a, w, NE)[1]; z1 = read(tr, b, w, NE)[1]
                        assert all(y == lam * x for x, y in zip(z0, z1))
                        gz = 0
                        for x in z0: gz = math.gcd(gz, x)
                        if gz != lam.denominator: continue
                        basis, c, g = crow_ab(edges, tr, a, b, w)
                        ck = char_kill(c)
                        if ck: key = "char%d" % ck[0]
                        elif not q_unit(c): key = 'Qbar'
                        else:
                            key = 'UNIT'; units.append((edges, a, b, ''.join(LET[l] for l in w), str(lam)))
                            if verbose: print('UNIT', rk, edges, a, b, ''.join(LET[l] for l in w), lam, flush=True)
                        k2 = (rk, str(lam), key); res[k2] = res.get(k2, 0) + 1
    return res, units


if __name__ == "__main__":
    n = int(sys.argv[1]); mr = int(sys.argv[2])
    nt = int(sys.argv[3]) if len(sys.argv) > 3 else 3
    sd = int(sys.argv[4]) if len(sys.argv) > 4 else 1
    md = sys.argv[5] if len(sys.argv) > 5 else 'tail'
    res, units = run(n, mr, nt, sd, mode=md)
    for k in sorted(res): print(k, res[k])
    print('units', len(units))
