# Census v2: decide exactly whether the abelianized cylinder row c^ab is unimodular over Z[s^+-,t^+-]
# (equivalently: no character into the units of any field kills c).  Non-covering graphs only
# (some vertex of degree < 4, so H has infinite index in F), words of length <= LMAX.
# One output line per configuration:  rank lam len class [detail] edges v0 v1 word
#   class: char<q>  (killed over F_q, q<=7)  |  Qbar (killed over Qbar)  |  bad<p,...> (Q-unit, killed mod p)
#          |  ZUNIT (unimodular over Z: passes every character test)  |  noN (resultant method inconclusive)
# usage: python3 census2.py n minrank maxrank per_h seed LMAX
import sys, random, math
from fc import *
from census import LAMS, rword
n, mr, Mr, per, seed, LMAX = [int(x) for x in sys.argv[1:7]]
rng = random.Random(seed)
for edges in graphs(n, mr):
    NE = len(edges); tr = mk(edges); rk = NE - n + 1
    if rk > Mr or NE == 2 * n: continue
    for root, par, gens in comps(n, tr):
        if len(gens) < 2: continue
        Z = [(read(tr, root[0], gw, NE)[1], read(tr, root[1], gw, NE)[1]) for gw in gens]
        for lam in LAMS:
            for h in nullvecs(Z, NE, lam):
                if sum(abs(x) for x in h) > 12: continue
                for it in range(per):
                    a, b, w = rword(tr, root, gens, h, rng, 1 + it % 2)
                    if len(w) < 4 or len(w) > LMAX or pp(w): continue
                    z0 = read(tr, a, w, NE)[1]; gz = 0
                    for x in z0: gz = math.gcd(gz, x)
                    if gz != lam.denominator: continue
                    basis, c, g = crow_ab(edges, tr, a, b, w)
                    ck = char_kill(c, (2, 3, 5, 7))
                    if ck: key = 'char%d' % ck[0]
                    else:
                        zu, info = z_unit(c)
                        if zu is True: key = 'ZUNIT'
                        elif zu is None: key = 'noN'
                        elif info == 'Qbar': key = 'Qbar'
                        else: key = 'bad' + ','.join(map(str, info))
                    print(rk, lam, len(w), key, edges, a, b, ''.join(LET[l] for l in w), flush=True)
