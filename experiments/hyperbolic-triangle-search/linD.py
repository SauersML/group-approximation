# linD.py (sage -python linD.py <mode>): homomorphisms G -> GL_d(K) for the triangles of
# lin4.py, for modules where every element of order 7 has d distinct eigenvalues.
#   mode d6c2  : d = 6, K = closure of F_2, A_7 and A_8 on the 6-dim heart of F_2^8 (unique
#                6-dim irreducible in char 2; only irreducible restrictions are covered).
#   mode d7c0  : d = 7, K = Q(zeta_7) (char 0): A_7 on F^7 = 6+1, A_8 on the 7-dim heart. These
#                are the only faithful 7-dim modules, so this is all of Hom(G, GL_7(C)).
#   mode d7p<p>: the same modules over F_p, p = 1 mod 7 (both are semisimple for p odd, p != 7).
# Parametrisation as in lin4.py: in the eigenbasis of t = alpha(q)^e1, beta = beta_1^h with h in
# the diagonal torus. For modules 6+1 the torus elements scalar on each summand centralise
# beta_1(B) and v, so the coordinates of eigenvalues 1 and w are normalised to 1 (NORM = 2);
# for irreducible modules only one coordinate is normalised (NORM = 1).
from sage.all import *
import itertools, sys, time

def plist(g, n): return [int(libgap.OnPoints(i, g)) for i in range(1, n + 1)]

def permmat(g, n, F):
    L = plist(g, n); M = zero_matrix(F, n)
    for i in range(n): M[i, L[i] - 1] = 1          # row convention: M(gh) = M(g) M(h)
    return M

def heart0(g, F):   # 7-dim sum-zero module of S_8, basis e_i - e_8
    M = permmat(g, 8, F); R = zero_matrix(F, 7)
    for i in range(7):
        b = vector(F, [1 if k == i else (-1 if k == 7 else 0) for k in range(8)]) * M
        for k in range(7): R[i, k] = b[k]
    return R

def heart2(g, F):   # 6-dim even-weight / all-ones module over F_2, basis e_i + e_8, i <= 6
    M = permmat(g, 8, F); R = zero_matrix(F, 6)
    for i in range(6):
        b = vector(F, [1 if k in (i, 7) else 0 for k in range(8)]) * M
        for k in range(6): R[i, k] = b[k] + b[6]
    return R

def relators(G, pair):
    F = libgap.Range(libgap.IsomorphismFpGroupByGenerators(G, pair))
    return [list(libgap.LetterRepAssocWord(r).sage()) for r in libgap.RelatorsOfFpGroup(F)]

def analyse(tag, mods, pairs, groups, e, K, om, d, norm, words, tw=(0, 0, 0)):
    # tw = (a,b,c): projective mu_7-twist; the B-lift of q^e1 is w^a alpha(q)^e1, the C-lift of
    # r^e2 is w^b beta(y_B)^e2 and the C-lift of p^e3 is w^c alpha(p)^e3 (G -> PGL_d).
    (mA, mB, mC), (pA, pB, pC), (GA, GB, GC) = mods, pairs, groups
    e1, e2, e3 = e
    P = mA(pA[0], K); Q = mA(pA[1], K); X0 = mB(pB[0], K); Y0 = mB(pB[1], K)
    Xc = mC(pC[0], K); Yc = mC(pC[1], K)
    for Z, nm in [(P, "A"), (Q, "A"), (X0, "B"), (Y0, "B"), (Xc, "C"), (Yc, "C")]:
        assert Z**7 == 1 and Z != 1
    t = om**tw[0] * Q**e1; v = om**tw[2] * P**e3; Y0e = om**tw[1] * Y0**e2
    if t.charpoly() != X0.charpoly(): return "charpoly(q^e1) != charpoly(x_B)"
    if v.charpoly() != Yc.charpoly(): return "charpoly(p^e3) != charpoly(y_C)"
    if Y0e.charpoly() != Xc.charpoly(): return "charpoly(r^e2) != charpoly(x_C)"
    roots = [r for r, m in t.charpoly().roots(K)]
    if len(roots) != d or any(m != 1 for r, m in t.charpoly().roots(K)):
        return "eigenvalues of t not distinct in K"
    expo = lambda z: [i for i in range(7) if om**i == z][0]
    order = sorted(roots, key=expo)
    def eigb(T):
        cols = []
        for lam in order:
            ker = (T - lam * identity_matrix(K, d)).right_kernel()
            assert ker.dimension() == 1
            cols.append(ker.basis()[0])
        return matrix(K, cols).transpose()
    S = eigb(t); S1 = eigb(X0)
    M = S1.inverse() * Y0e * S1; N = S.inverse() * v * S
    nv = d - norm
    PR = PolynomialRing(K, ['h%d' % i for i in range(nv)] + ['g%d' % i for i in range(nv)],
                        order='degrevlex')
    hs = PR.gens()[:nv]; gs = PR.gens()[nv:]
    H = diagonal_matrix(PR, [1] * norm + list(hs)); Hi = diagonal_matrix(PR, [1] * norm + list(gs))
    Mp = [None] + [H * M.change_ring(PR)**i * Hi for i in range(1, 7)]
    Np = [None] + [N.change_ring(PR)**j for j in range(1, 7)]
    Xp = [None] + [Xc**i for i in range(1, 7)]; Yp = [None] + [Yc**j for j in range(1, 7)]
    gens = [hs[i] * gs[i] - 1 for i in range(nv)]
    for wd in words:
        Mw = identity_matrix(PR, d); Tw = identity_matrix(K, d)
        for s in range(0, len(wd), 2):
            Mw = Mw * Mp[wd[s]] * Np[wd[s + 1]]; Tw = Tw * Xp[wd[s]] * Yp[wd[s + 1]]
        gens.append(Mw.trace() - Tw.trace())
    I = PR.ideal(gens)
    gb = I.groebner_basis()
    if list(gb) == [1]: return "trace ideal = (1): no hom"
    dim = I.dimension()
    res = "trace ideal NOT (1): dimension %d" % dim
    if dim == 0:
        res += ", %d points with multiplicity" % I.vector_space_dimension()
        if K.is_finite():
            V = I.variety(); relC = relators(GC, pC)
            chk = []
            for pt in V:
                HL = diagonal_matrix(K, [1] * norm + [pt[h] for h in hs])
                U = HL * M * HL.inverse()
                ok = True
                for r in relC:
                    R = identity_matrix(K, d)
                    for l in r: R = R * {1: U, -1: U.inverse(), 2: N, -2: N.inverse()}[l]
                    ok = ok and R == 1
                chk.append(ok)
            res += ", K-rational points verified against R_C: %s" % chk
    return res

if __name__ == "__main__":
    mode = sys.argv[1]; which = sys.argv[2] if len(sys.argv) > 2 else "cands"
    A8 = libgap.AlternatingGroup(8); A7 = libgap.AlternatingGroup(7); E = libgap.eval
    t0 = time.time()
    if mode == "d6c2":
        Rx = PolynomialRing(GF(2), 'x'); xx = Rx.gen()
        K = GF(8, 'w', modulus=xx**3 + xx + 1); om = K.gen(); d, norm = 6, 1
        mA = mB = mC7 = lambda g, F: heart2(g, F); mC = mA
    elif mode == "d7c0":
        K = CyclotomicField(7, 'z'); om = K.gen(); d, norm = 7, 2
    elif mode.startswith("d7p"):
        p = int(mode[3:]); assert p % 2 == 1 and p != 7
        k = Mod(p, 7).multiplicative_order()
        K = GF(p**k, 'a'); om = K.multiplicative_generator()**((p**k - 1) // 7); d, norm = 7, 2
    if mode.startswith("d7"):
        mA = mB = mC7 = lambda g, F: permmat(g, 7, F); mC = lambda g, F: heart0(g, F)
    words = [(i, j) for i in range(1, 7) for j in range(1, 7)]
    words += [(i, j, k, l) for i in range(1, 4) for j in range(1, 4) for k in range(1, 4)
              for l in range(1, 4)]
    if which == "cal":
        cal = [E("(1,7,4,6,5,2,3)"), E("(1,2,4,7,6,3,5)"), E("(1,6,3,2,7,4,5)")]
        pr = ([cal[0], cal[1]], [cal[1]**3, cal[2]], [cal[2]**5, cal[0]**2])
        print("CAL twisted A7 triple ::", analyse("cal", (mA, mB, mC7), pr, (A7, A7, A7),
              (3, 5, 2), K, om, d, norm, words)); sys.stdout.flush()
        c8 = [E("(1,5,2,4,7,6,8)"), E("(1,6,4,7,2,5,3)"), E("(1,5,4,8,2,3,7)")]
        mH = mC if mode.startswith("d7") else mA
        n8 = 1 if mode.startswith("d7") else norm
        print("CAL literal A8 triple ::", analyse("cal8", (mH, mH, mH),
              ([c8[0], c8[1]], [c8[1], c8[2]], [c8[2], c8[0]]), (A8, A8, A8), (1, 1, 1),
              K, om, d, n8, words)); sys.stdout.flush()
    elif which in ("twist", "twistorbits"):
        # projective mu_7-twists (a,b,c) for each candidate: G_i -> PGL_d(K). "twistorbits" takes
        # one representative per orbit of (Z/7)^x acting by multiplication (58 orbits). This is valid
        # when the modules are rational (permutation modules): Galois conjugation w -> w^j maps the
        # zero set of twist (a,b,c) onto that of (ja,jb,jc). Optional argv[3] = candidate indices "1,2".
        ns = {}; exec(open("cands.py").read(), ns)
        sel = [int(s) for s in sys.argv[3].split(",")] if len(sys.argv) > 3 else [1, 2, 3, 4]
        twl = list(itertools.product(range(7), repeat=3))
        if which == "twistorbits":
            twl = sorted(set(min(tuple((j * x) % 7 for x in tw) for j in range(1, 7)) for tw in twl))
            print("twist orbit representatives:", len(twl)); sys.stdout.flush()
        for k, c in enumerate(ns["CANDS"], 1):
            if k not in sel: continue
            pr = tuple([E(s) for s in c[X]] for X in "ABC")
            tally = {}
            for tw in twl:
                res = analyse("c", (mA, mB, mC), pr, (A7, A7, A8), tuple(c["e"]), K, om, d,
                              norm, words, tw)
                tally[res] = tally.get(res, 0) + 1
                if "NOT (1)" in res:
                    print("CAND%d %s twist %s :: %s" % (k, mode, tw, res)); sys.stdout.flush()
            print("CAND%d %s twist tally :: %s" % (k, mode, tally)); sys.stdout.flush()
    else:
        ns = {}; exec(open("cands.py").read(), ns)
        for k, c in enumerate(ns["CANDS"], 1):
            pr = tuple([E(s) for s in c[X]] for X in "ABC")
            print("CAND%d %s ::" % (k, mode), analyse("c", (mA, mB, mC), pr, (A7, A7, A8),
                  tuple(c["e"]), K, om, d, norm, words)); sys.stdout.flush()
    print("LIND_DONE %s %s %.1fs" % (mode, which, time.time() - t0))
