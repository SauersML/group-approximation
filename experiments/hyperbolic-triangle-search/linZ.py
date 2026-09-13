# linZ.py (sage -python linZ.py <cand indices> [twist a,b,c]): integral Nullstellensatz integer N for
# Hom(G_i, GL_7) with modules 1+6 (A, B) and 7 (C), as in linear-quotient-exclusion-lifts-from-char-zero (L2).
# Integral model, no eigenbases:
#   P, Q = permutation matrices of alpha(p), alpha(q) on 7 points; t0 = Q^e1 (a 7-cycle matrix).
#   X0, Y0 = permutation matrices of beta_0(x_B), beta_0(y_B); pi = permutation matrix with pi X0 pi^-1 = t0.
#   Every beta with beta(x_B) = t0 is h (pi beta_0 pi^-1) h^-1 with h in C(t0) = circulants in t0
#   (t0 has distinct eigenvalues over F_p-bar for p != 7); h = sum c_i t0^i, k = sum d_i t0^i, h k = 1.
#   u = h Y1^e2 k with Y1 = pi Y0 pi^-1, v = P^e3; equations tr w(u,v) = tr w(Xc, Yc) (integers, heart of 8).
# Normalisation (scalars and J = sum t0^i centralise beta_1(B) and v): sum c_i = 1 and c_0 + ... is left free.
# A strong Groebner basis over ZZ that contains an integer N means: no such hom over any field of
# characteristic not dividing N (and N = 1: none at all). Twists (a,b,c) need zeta_7; not handled here.
from sage.all import *
import sys, time
E = libgap.eval
def plist(g, n): return [int(libgap.OnPoints(i, g)) for i in range(1, n + 1)]
def permmat(g, n, R):
    L = plist(g, n); M = zero_matrix(R, n)
    for i in range(n): M[i, L[i] - 1] = 1
    return M
def heart0(g, R):
    M = permmat(g, 8, R); Rm = zero_matrix(R, 7)
    for i in range(7):
        b = vector(R, [1 if k == i else (-1 if k == 7 else 0) for k in range(8)]) * M
        for k in range(7): Rm[i, k] = b[k]
    return Rm
def perm_conj(X, T, n):   # permutation matrix pi with pi X pi^-1 = T for n-cycles X, T (row convention)
    lx = [list(X.row(i)).index(1) for i in range(n)]; lt = [list(T.row(i)).index(1) for i in range(n)]
    # X: i -> lx[i]; T: j -> lt[j]; map the cycle of X starting at 0 onto the cycle of T starting at 0
    sig = [None] * n; i, j = 0, 0
    for s in range(n):
        sig[i] = j; i, j = lx[i], lt[j]
    Pm = zero_matrix(ZZ, n)
    for i in range(n): Pm[i, sig[i]] = 1
    return Pm
def system(c, R, nwords2=3):
    pA = [E(s) for s in c["A"]]; pB = [E(s) for s in c["B"]]; pC = [E(s) for s in c["C"]]
    e1, e2, e3 = c["e"]
    P = permmat(pA[0], 7, ZZ); Q = permmat(pA[1], 7, ZZ); X0 = permmat(pB[0], 7, ZZ); Y0 = permmat(pB[1], 7, ZZ)
    Xc = heart0(pC[0], ZZ); Yc = heart0(pC[1], ZZ)
    t0 = Q**e1
    # GAP: g with x_B^g = (y_A)^e1, i.e. g^-1 x_B g = y_A^e1. Row convention M(gh) = M(g) M(h) gives
    # M(g)^-1 X0 M(g) = t0, so pi = M(g)^-1 satisfies pi X0 pi^-1 = t0.
    g = libgap.RepresentativeAction(libgap.SymmetricGroup(7), pB[0], pA[1]**e1)
    assert g != libgap.eval("fail")
    pi = permmat(g, 7, ZZ).inverse()
    assert pi * X0 * pi.inverse() == t0
    Y1 = pi * Y0 * pi.inverse(); v = P**e3
    cs = R.gens()[:7]; ds = R.gens()[7:14]
    pw = [identity_matrix(ZZ, 7)] + [t0**i for i in range(1, 7)]
    h = sum(cs[i] * pw[i].change_ring(R) for i in range(7)); k = sum(ds[i] * pw[i].change_ring(R) for i in range(7))
    eqs = list((h * k - identity_matrix(R, 7)).row(0))       # circulant: first row determines h k
    eqs.append(sum(cs) - 1)
    U = [None] + [h * (Y1**(e2 * i)).change_ring(R) * k for i in range(1, 7)]
    V = [None] + [(v**j).change_ring(R) for j in range(1, 7)]
    Xp = [None] + [Xc**i for i in range(1, 7)]; Yp = [None] + [Yc**j for j in range(1, 7)]
    words = [(i, j) for i in range(1, 7) for j in range(1, 7)]
    words += [(i, j, kk, l) for i in range(1, nwords2 + 1) for j in range(1, nwords2 + 1)
              for kk in range(1, nwords2 + 1) for l in range(1, nwords2 + 1)]
    for wd in words:
        Mw = identity_matrix(R, 7); Tw = identity_matrix(ZZ, 7)
        for s in range(0, len(wd), 2):
            Mw = Mw * U[wd[s]] * V[wd[s + 1]]; Tw = Tw * Xp[wd[s]] * Yp[wd[s + 1]]
        eqs.append(Mw.trace() - Tw.trace())
    return eqs
def system_tw(c, R, tw, nwords2=3):
    # Projective mu_7-twist (a,b,c) over Z[z]/Phi_7(z): beta(x_B) = z^a t0 via the diagonal D with
    # D t0 D^-1 = z^a t0 (delta_{i_k} = z^{-ak} along the cycle i_0 -> i_1 -> ... of t0), C(z^a t0) = C(t0);
    # u = z^b h (D Y1 D^-1)^e2 k, v = z^c P^e3. The last generator of R is z.
    pA = [E(s) for s in c["A"]]; pB = [E(s) for s in c["B"]]; pC = [E(s) for s in c["C"]]
    e1, e2, e3 = c["e"]; a, b, cc = tw
    P = permmat(pA[0], 7, ZZ); Q = permmat(pA[1], 7, ZZ); X0 = permmat(pB[0], 7, ZZ); Y0 = permmat(pB[1], 7, ZZ)
    Xc = heart0(pC[0], ZZ); Yc = heart0(pC[1], ZZ)
    t0 = Q**e1
    g = libgap.RepresentativeAction(libgap.SymmetricGroup(7), pB[0], pA[1]**e1)
    pi = permmat(g, 7, ZZ).inverse(); assert pi * X0 * pi.inverse() == t0
    Y1 = pi * Y0 * pi.inverse(); v = P**e3
    z = R.gens()[14]; cs = R.gens()[:7]; ds = R.gens()[7:14]
    sig = [list(t0.row(i)).index(1) for i in range(7)]
    order = [0]
    for s in range(6): order.append(sig[order[-1]])
    dl = [None] * 7; dli = [None] * 7
    for kpos, i in enumerate(order):
        dl[i] = z**((6 * a * kpos) % 7); dli[i] = z**((a * kpos) % 7)
    D = diagonal_matrix(R, dl); Di = diagonal_matrix(R, dli)
    # numeric check over GF(29), z -> primitive 7th root: D t0 D^-1 = z^a t0
    F = GF(29); w = F.multiplicative_generator()**4; sub = lambda M: M.apply_map(lambda f: F(f(*([0] * 14 + [w]))))
    assert sub(D * t0.change_ring(R) * Di) == w**a * t0.change_ring(F)
    Y1t = D * Y1.change_ring(R) * Di
    pw = [identity_matrix(ZZ, 7)] + [t0**i for i in range(1, 7)]
    h = sum(cs[i] * pw[i].change_ring(R) for i in range(7)); k = sum(ds[i] * pw[i].change_ring(R) for i in range(7))
    eqs = list((h * k - identity_matrix(R, 7)).row(0)); eqs.append(sum(cs) - 1)
    eqs.append(sum(z**i for i in range(7)))
    U = [None] + [z**((b * i) % 7) * h * Y1t**(e2 * i) * k for i in range(1, 7)]
    V = [None] + [z**((cc * j) % 7) * (v**j).change_ring(R) for j in range(1, 7)]
    Xp = [None] + [Xc**i for i in range(1, 7)]; Yp = [None] + [Yc**j for j in range(1, 7)]
    words = [(i, j) for i in range(1, 7) for j in range(1, 7)]
    words += [(i, j, kk, l) for i in range(1, nwords2 + 1) for j in range(1, nwords2 + 1)
              for kk in range(1, nwords2 + 1) for l in range(1, nwords2 + 1)]
    for wd in words:
        Mw = identity_matrix(R, 7); Tw = identity_matrix(ZZ, 7)
        for s in range(0, len(wd), 2):
            Mw = Mw * U[wd[s]] * V[wd[s + 1]]; Tw = Tw * Xp[wd[s]] * Yp[wd[s + 1]]
        eqs.append(Mw.trace() - Tw.trace())
    return eqs

if __name__ == "__main__" and len(sys.argv) > 1 and sys.argv[1] == "twist":
    # sage -python linZ.py twist <cand indices>: integral GB for the 58 Galois orbit representatives
    import itertools
    ns = {}; exec(open("cands.py").read(), ns)
    R2 = PolynomialRing(ZZ, ['c%d' % i for i in range(7)] + ['d%d' % i for i in range(7)] + ['z'], order='degrevlex')
    twl = sorted(set(min(tuple((j * x) % 7 for x in tw) for j in range(1, 7))
                     for tw in itertools.product(range(7), repeat=3)))
    for kk in [int(s) for s in sys.argv[2].split(",")]:
        tally = {}; t0 = time.time()
        for tw in twl:
            gb = R2.ideal(system_tw(ns["CANDS"][kk - 1], R2, tw)).groebner_basis()
            ints = [f for f in gb if f.is_constant()]
            key = "N=%s" % (factor(ZZ(ints[0])) if ints else "none")
            tally[key] = tally.get(key, 0) + 1
            if key != "N=1": print("CAND%d twist %s :: integral GB %s" % (kk, tw, key)); sys.stdout.flush()
        print("CAND%d integral twist tally over %d orbit reps :: %s (%.1fs)" % (kk, len(twl), tally, time.time() - t0))
        sys.stdout.flush()
    print("LINZ_TWIST_DONE"); sys.exit(0)

if __name__ == "__main__":
    nw2 = int(sys.argv[2]) if len(sys.argv) > 2 else 3
    ns = {}; exec(open("cands.py").read(), ns)
    R = PolynomialRing(ZZ, ['c%d' % i for i in range(7)] + ['d%d' % i for i in range(7)], order='degrevlex')
    if sys.argv[1] == "cal":
        # Calibration: the literal (A7,A7,A7) triple of tri_cal2.g with twisted pairs, e = (3,5,2). The C
        # pair consists of A7 elements (fixing 8), whose heart-of-8 module is the permutation module of 7
        # points, so p,q,r -> permutation matrices is a solution: the ideal must NOT be (1).
        CAL = {"A": ["(1,7,4,6,5,2,3)", "(1,2,4,7,6,3,5)"], "B": ["(1,2,4,7,6,3,5)^3", "(1,6,3,2,7,4,5)"],
               "C": ["(1,6,3,2,7,4,5)^5", "(1,7,4,6,5,2,3)^2"], "e": [3, 5, 2]}
        ns["CANDS"] = [CAL]; sel = [1]
    else:
        sel = [int(s) for s in sys.argv[1].split(",")]
    for kk in sel:
        t0 = time.time()
        eqs = system(ns["CANDS"][kk - 1], R, nw2)
        RQ = R.change_ring(QQ); gbq = RQ.ideal([RQ(f) for f in eqs]).groebner_basis()
        print("CAND%d rational GB = %s (%.1fs)" % (kk, "[1]" if list(gbq) == [1] else "not [1], len %d" % len(gbq), time.time() - t0)); sys.stdout.flush()
        gb = R.ideal(eqs).groebner_basis()
        ints = [f for f in gb if f.is_constant()]
        N = ints[0] if ints else None
        print("CAND%d integral GB: %d elements, integer element N = %s, factor = %s (%.1fs)" %
              (kk, len(gb), N, factor(ZZ(N)) if N else None, time.time() - t0)); sys.stdout.flush()
    print("LINZ_DONE")
