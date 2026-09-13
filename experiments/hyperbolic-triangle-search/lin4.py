# lin4.py (run with `sage -python lin4.py`): all homomorphisms G -> GL_4(K), K = algebraic
# closure of F_2, for triangles G = <p,q,r | R_A(p,q), R_B(q^e1,r), R_C(r^e2,p^e3)> with
# vertex groups A_7 / A_8 given by generating pairs of 7-elements. Lane ex-hyperbolic-triangle-search.
#
# Every faithful 4-dim module of A_7 or A_8 in char 2 is 4 or 4* (restriction of A_8 = L_4(2)).
# Fix alpha = rho_eA on A: P = alpha(p), Q = alpha(q); t = Q^e1. Every beta: B -> GL_4(K) of type
# eB with beta(x_B) = t is g beta0 g^-1 with g = S H S'^-1, S, S' eigenbases of t and beta0(x_B)
# (eigenvalues distinct), H = diag(h1,h2,h3,1). In the t-eigenbasis, u = r^e2 = H M H^-1 with
# M = S'^-1 beta0(y_B)^e2 S', v = N = S^-1 P^e3 S. A hom exists iff (H M H^-1, N) satisfies R_C.
# Necessary: traces of words equal those of rho_eC(x_C), rho_eC(y_C). The ideal of these trace
# equations (with h_i g_i = 1) is computed; GB = [1] proves no hom for (eA,eB,eC); otherwise
# its points are found and checked against the relators of C.
from sage.all import *
import itertools, sys, time

F2 = GF(2)
Rx = PolynomialRing(F2, 'x'); xx = Rx.gen()
K = GF(8, 'w', modulus=xx**3 + xx + 1); w = K.gen()
A8 = libgap.AlternatingGroup(8); A7 = libgap.AlternatingGroup(7)
ISO = libgap.IsomorphismGroups(A8, libgap.SL(4, 2))

def rho(g, dual):
    m = libgap.Image(ISO, g)
    M = matrix(F2, [[F2(int(libgap.IntFFE(e))) for e in row] for row in m])
    return M.inverse().transpose() if dual else M

def relators(G, pair):
    F = libgap.Range(libgap.IsomorphismFpGroupByGenerators(G, pair))
    return [list(libgap.LetterRepAssocWord(r).sage()) for r in libgap.RelatorsOfFpGroup(F)]

def evalword(word, X, Y):
    I = identity_matrix(X.base_ring(), X.nrows()); R = I
    Xi, Yi = X.inverse(), Y.inverse()
    for l in word:
        R = R * {1: X, -1: Xi, 2: Y, -2: Yi}[l]
    return R

def eigbasis(T, order):
    cols = []
    for lam in order:
        ker = (T - lam * identity_matrix(K, 4)).right_kernel()
        if ker.dimension() != 1: return None
        cols.append(ker.basis()[0])
    return matrix(K, cols).transpose()

def analyse(label, GA, pairA, GB, pairB, GC, pairC, e, extra_words=True):
    e1, e2, e3 = e
    relC = relators(GC, pairC)
    out = []
    for eA, eB, eC in itertools.product([0, 1], repeat=3):
        P = rho(pairA[0], eA).change_ring(K); Q = rho(pairA[1], eA).change_ring(K)
        X0 = rho(pairB[0], eB).change_ring(K); Y0 = rho(pairB[1], eB).change_ring(K)
        Xc = rho(pairC[0], eC).change_ring(K); Yc = rho(pairC[1], eC).change_ring(K)
        t = Q**e1; v = P**e3
        tag = "%s eA=%d eB=%d eC=%d" % (label, eA, eB, eC)
        if t.charpoly() != X0.charpoly():
            out.append((tag, "charpoly(q^e1) != charpoly(x_B)")); continue
        if v.charpoly() != Yc.charpoly():
            out.append((tag, "charpoly(p^e3) != charpoly(y_C)")); continue
        if (Y0**e2).charpoly() != Xc.charpoly():
            out.append((tag, "charpoly(r^e2) != charpoly(x_C)")); continue
        order = sorted([r for r, m in t.charpoly().roots(K)], key=lambda z: z.log(w))
        S = eigbasis(t, order); S1 = eigbasis(X0, order)
        M = S1.inverse() * Y0**e2 * S1; N = S.inverse() * v * S
        PR = PolynomialRing(K, 'h1,h2,h3,g1,g2,g3', order='degrevlex')
        h1, h2, h3, g1, g2, g3 = PR.gens()
        H = diagonal_matrix(PR, [h1, h2, h3, 1]); Hi = diagonal_matrix(PR, [g1, g2, g3, 1])
        Mp = [None] + [H * M.change_ring(PR)**i * Hi for i in range(1, 7)]
        Np = [None] + [N.change_ring(PR)**j for j in range(1, 7)]
        Xp = [None] + [Xc**i for i in range(1, 7)]; Yp = [None] + [Yc**j for j in range(1, 7)]
        gens = [h1 * g1 - 1, h2 * g2 - 1, h3 * g3 - 1]
        words = [(i, j) for i in range(1, 7) for j in range(1, 7)]
        if extra_words:
            words += [(i, j, k, l) for i in range(1, 4) for j in range(1, 4)
                      for k in range(1, 4) for l in range(1, 4)]
        for wd in words:
            Mw = identity_matrix(PR, 4); Tw = identity_matrix(K, 4)
            for s in range(0, len(wd), 2):
                Mw = Mw * Mp[wd[s]] * Np[wd[s + 1]]; Tw = Tw * Xp[wd[s]] * Yp[wd[s + 1]]
            gens.append(Mw.trace() - Tw.trace())
        I = PR.ideal(gens)
        gb = I.groebner_basis()
        if list(gb) == [1]:
            out.append((tag, "trace ideal = (1): no hom")); continue
        d = I.dimension()
        if d != 0:
            out.append((tag, "trace ideal has dimension %d (needs more words)" % d)); continue
        npts = I.vector_space_dimension()
        found = []
        for k in [3, 6, 9, 12, 18, 24]:
            L = GF(2**k, 'z')
            emb = K.hom([K.modulus().change_ring(L).roots()[0][0]], L)
            PL = PolynomialRing(L, PR.variable_names(), order='degrevlex')
            try:
                V = PL.ideal([PL({ex: emb(c) for ex, c in f.dict().items()}) for f in gens]).variety()
            except Exception as ex:
                print("variety failed over GF(2^%d): %s" % (k, ex)); continue
            if len(V) >= 1:
                ML = M.apply_map(emb); NL = N.apply_map(emb)
                for pt in V:
                    HL = diagonal_matrix(L, [pt[PL.gen(0)], pt[PL.gen(1)], pt[PL.gen(2)], 1])
                    U = HL * ML * HL.inverse()
                    ok = all(evalword(r, U, NL) == identity_matrix(L, 4) for r in relC)
                    found.append((k, ok))
            if len(V) == npts: break
        out.append((tag, "0-dim trace ideal, %d points (mult), checked over GF(2^k): %s" % (npts, found)))
    return out

if __name__ == "__main__":
    mode = sys.argv[1] if len(sys.argv) > 1 else "cal"
    P7 = lambda s: libgap.eval(s)
    t0 = time.time()
    if mode == "cal":
        # literal (A8,A8,A8) triple of cal1.g's seed must give homs (trivially H = 1 works)
        tr = libgap.eval("""function() local rs, els, tr, A8;
          A8 := AlternatingGroup(8); rs := RandomSource(IsMersenneTwister, 20260913);
          els := Filtered(AsList(A8), g -> Order(g) = 7);
          repeat tr := List([1..3], i -> Random(rs, els));
          until Size(Group(tr[1], tr[2])) = 20160 and Size(Group(tr[2], tr[3])) = 20160
                and Size(Group(tr[3], tr[1])) = 20160;
          return tr; end""")()
        tr = [tr[0], tr[1], tr[2]]
        print("CAL triple", tr)
        for tag, res in analyse("CAL literal A8 triple", A8, [tr[0], tr[1]], A8, [tr[1], tr[2]],
                                A8, [tr[2], tr[0]], (1, 1, 1)):
            print(tag, "::", res); sys.stdout.flush()
        cal = [P7("(1,7,4,6,5,2,3)"), P7("(1,2,4,7,6,3,5)"), P7("(1,6,3,2,7,4,5)")]
        e = (3, 5, 2)   # twisted pairs so the literal triple is a hom for a nontrivial e
        for tag, res in analyse("CAL literal A7 triple twisted e=(3,5,2)", A7, [cal[0], cal[1]], A7,
                                [cal[1]**3, cal[2]], A7, [cal[2]**5, cal[0]**2], e):
            print(tag, "::", res); sys.stdout.flush()
    else:
        exec(open("cands.py").read())
        for k, c in enumerate(CANDS, 1):
            A = [P7(s) for s in c["A"]]; B = [P7(s) for s in c["B"]]; C = [P7(s) for s in c["C"]]
            for tag, res in analyse("CAND%d" % k, A7, A, A7, B, A8, C, tuple(c["e"])):
                print(tag, "::", res); sys.stdout.flush()
    print("LIN4_DONE %.1fs" % (time.time() - t0))
