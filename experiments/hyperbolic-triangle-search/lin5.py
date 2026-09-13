# lin5.py (sage -python lin5.py cal|cands): Hom(G, GL_5(K)), K = closure of F_2, vertex modules 4+1 or 4*+1.
# This is the last low-dimensional case: in characteristic 2, faithful modules of dimension <= 7 of the
# 4-type are semisimple 4 + 1^k (H^1(A_7,4) = H^1(A_7,4*) = H^1(A_8,4) = 0), and W_X = [V,X] is
# 4-dimensional; either all W_X coincide (dimension 4, lin4.py) or W_A + W_B + W_C is a 5-dimensional
# G-invariant subspace on which the vertex groups act as 4 + 1 (this script).
# Parametrisation: t = alpha(q)^e1 has eigenvalue 1 with multiplicity 2 and three simple eigenvalues, so
# C(t) = GL_2 x T^3 in the eigenbasis; every beta with beta(x_B) = t is g beta_0 g^-1, g = S H S'^-1,
# H = [[a,b],[c,d]] + diag(h2,h3,h4). Trace equations against rho_eC + 1 as in lin4.py.
from sage.all import *
import itertools, sys, time
F2 = GF(2); Rx = PolynomialRing(F2, 'x'); xx = Rx.gen()
K = GF(8, 'w', modulus=xx**3 + xx + 1); w = K.gen()
A8 = libgap.AlternatingGroup(8); A7 = libgap.AlternatingGroup(7)
ISO = libgap.IsomorphismGroups(A8, libgap.SL(4, 2))
def rho5(g, dual):
    m = libgap.Image(ISO, g)
    M = matrix(F2, [[F2(int(libgap.IntFFE(e))) for e in row] for row in m])
    if dual: M = M.inverse().transpose()
    return block_diagonal_matrix(M, identity_matrix(F2, 1)).change_ring(K)
def relators(G, pair):
    F = libgap.Range(libgap.IsomorphismFpGroupByGenerators(G, pair))
    return [list(libgap.LetterRepAssocWord(r).sage()) for r in libgap.RelatorsOfFpGroup(F)]
def basis5(T):
    ker = (T - identity_matrix(K, 5)).right_kernel()
    if ker.dimension() != 2: return None
    cols = list(ker.basis())
    others = sorted([r for r, m in T.charpoly().roots(K) if r != 1], key=lambda z: z.log(w))
    for lam in others:
        kk = (T - lam * identity_matrix(K, 5)).right_kernel()
        if kk.dimension() != 1: return None
        cols.append(kk.basis()[0])
    return matrix(K, cols).transpose()
def analyse(label, GA, pA, GB, pB, GC, pC, e):
    e1, e2, e3 = e; out = []
    words = [(i, j) for i in range(1, 7) for j in range(1, 7)]
    words += [(i, j, k, l) for i in range(1, 4) for j in range(1, 4) for k in range(1, 4) for l in range(1, 4)]
    for eA, eB, eC in itertools.product([0, 1], repeat=3):
        P = rho5(pA[0], eA); Q = rho5(pA[1], eA); X0 = rho5(pB[0], eB); Y0 = rho5(pB[1], eB)
        Xc = rho5(pC[0], eC); Yc = rho5(pC[1], eC)
        t = Q**e1; v = P**e3; tag = "%s eA=%d eB=%d eC=%d" % (label, eA, eB, eC)
        if t.charpoly() != X0.charpoly(): out.append((tag, "charpoly(q^e1) != charpoly(x_B)")); continue
        if v.charpoly() != Yc.charpoly(): out.append((tag, "charpoly(p^e3) != charpoly(y_C)")); continue
        if (Y0**e2).charpoly() != Xc.charpoly(): out.append((tag, "charpoly(r^e2) != charpoly(x_C)")); continue
        S = basis5(t); S1 = basis5(X0)
        M = S1.inverse() * Y0**e2 * S1; N = S.inverse() * v * S
        PR = PolynomialRing(K, 'a,b,c,d,dl,h2,h3,h4,g2,g3,g4', order='degrevlex')
        a, b, c, d, dl, h2, h3, h4, g2, g3, g4 = PR.gens()
        H = block_diagonal_matrix(matrix(PR, [[a, b], [c, d]]), diagonal_matrix(PR, [h2, h3, h4]))
        Hi = block_diagonal_matrix(matrix(PR, [[d * dl, b * dl], [c * dl, a * dl]]), diagonal_matrix(PR, [g2, g3, g4]))
        gens = [dl * (a * d + b * c) - 1, h2 * g2 - 1, h3 * g3 - 1, h4 * g4 - 1]
        Mp = [None] + [H * (M**i).change_ring(PR) * Hi for i in range(1, 7)]
        Np = [None] + [(N**j).change_ring(PR) for j in range(1, 7)]
        Xp = [None] + [Xc**i for i in range(1, 7)]; Yp = [None] + [Yc**j for j in range(1, 7)]
        for wd in words:
            Mw = identity_matrix(PR, 5); Tw = identity_matrix(K, 5)
            for s in range(0, len(wd), 2):
                Mw = Mw * Mp[wd[s]] * Np[wd[s + 1]]; Tw = Tw * Xp[wd[s]] * Yp[wd[s + 1]]
            gens.append(Mw.trace() - Tw.trace())
        I = PR.ideal(gens); gb = I.groebner_basis()
        if list(gb) == [1]: out.append((tag, "trace ideal = (1): no hom")); continue
        out.append((tag, "trace ideal NOT (1): dimension %d" % I.dimension()))
    return out
if __name__ == "__main__":
    E = libgap.eval; t0 = time.time()
    if sys.argv[1] == "cal":
        tr = [E("(1,5,2,4,7,6,8)"), E("(1,6,4,7,2,5,3)"), E("(1,5,4,8,2,3,7)")]
        for tag, res in analyse("CAL literal A8 triple (4+1)", A8, [tr[0], tr[1]], A8, [tr[1], tr[2]], A8, [tr[2], tr[0]], (1, 1, 1)):
            print(tag, "::", res); sys.stdout.flush()
        cal = [E("(1,7,4,6,5,2,3)"), E("(1,2,4,7,6,3,5)"), E("(1,6,3,2,7,4,5)")]
        for tag, res in analyse("CAL twisted A7 triple (4+1)", A7, [cal[0], cal[1]], A7, [cal[1]**3, cal[2]], A7, [cal[2]**5, cal[0]**2], (3, 5, 2)):
            print(tag, "::", res); sys.stdout.flush()
    else:
        ns = {}; exec(open("cands.py").read(), ns)
        for k, c in enumerate(ns["CANDS"], 1):
            pr = [[E(s) for s in c[X]] for X in "ABC"]
            for tag, res in analyse("CAND%d" % k, A7, pr[0], A7, pr[1], A8, pr[2], tuple(c["e"])):
                print(tag, "::", res); sys.stdout.flush()
    print("LIN5_DONE %.1fs" % (time.time() - t0))
