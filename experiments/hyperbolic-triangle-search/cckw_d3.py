# cckw_d3.py (sage -python cckw_d3.py cal|survivors <p>): 3-dimensional representations over F_p-bar (p = 1 mod
# 5460, so all vertex modules split) of CCKW triangle groups G = <a,b,c | a^3,b^3,c^3, R_ab, R_bc, R_ca> that are
# faithful and absolutely irreducible on the three vertex groups A = <a,b>, B = <b,c>, C = <c,a>.
# As in linD.py: alpha = module at A (P = a, Q = b); beta = g beta_0 g^-1 with beta(b) = Q, g = S H S1^-1,
# H = diag(h1,h2,1); u = H M H^-1 (image of c), v = N (image of a) in the eigenbasis of Q; trace equations of
# words in (u,v) against the C-module; points verified on the relators of C. A verified point is a
# vertex-injective homomorphism G -> GL_3(F_q), hence a finite quotient.
from sage.all import *
import itertools, sys, time
E = libgap.eval
def mat(m, p): return matrix(GF(p), [[int(libgap.IntFFE(e)) for e in row] for row in m])
def vertex(rels_gap, i, j):
    # vertex group on generators i,j (1..3) from a GAP relator list over free group F
    return libgap.eval("""function(rels, i, j) local FF, rr, G0, iso, X;
        FF := FreeGroup("x", "y");
        rr := Filtered(rels, w -> IsSubset([i, j], Set(List(LetterRepAssocWord(w), AbsInt))));
        rr := List(rr, w -> MappedWord(w, GeneratorsOfGroup(F){[i, j]}, GeneratorsOfGroup(FF)));
        G0 := FF / rr; iso := IsomorphismPermGroup(G0); X := Image(iso);
        return [X, Image(iso, G0.1), Image(iso, G0.2)]; end""")(rels_gap, i, j)
def modules3(X, x, y, p):
    # faithful absolutely irreducible 3-dim modules of X over GF(p): images of x and y
    # faithfulness via conjugacy class representatives (never compute the order of a matrix group over GF(p))
    res = libgap.eval("""function(X, x, y, p) local L, gens, out, M, hom, reps;
        L := IrreducibleModules(X, GF(p), 3); gens := L[1]; out := [];
        reps := Filtered(List(ConjugacyClasses(X), Representative), g -> g <> One(X));
        for M in L[2] do
          if M.dimension = 3 and MTX.IsAbsolutelyIrreducible(M) then
            hom := GroupHomomorphismByImagesNC(X, GL(3, p), gens, M.generators);
            if ForAll(reps, g -> ImagesRepresentative(hom, g) <> One(GL(3, p))) then
              Add(out, [ImagesRepresentative(hom, x), ImagesRepresentative(hom, y)]);
            fi;
          fi;
        od; return out; end""")(X, x, y, p)
    return [(mat(r[0], p), mat(r[1], p)) for r in res]
def relators2(X, x, y):
    F2 = libgap.Range(libgap.IsomorphismFpGroupByGenerators(X, [x, y]))
    return [list(libgap.LetterRepAssocWord(r).sage()) for r in libgap.RelatorsOfFpGroup(F2)]
def eigb(T, K, order):
    cols = []
    for lam in order:
        ker = (T - lam * identity_matrix(K, 3)).right_kernel()
        if ker.dimension() != 1: return None
        cols.append(ker.basis()[0])
    return matrix(K, cols).transpose()
def analyse(label, rels_gap, p):
    K = GF(p); out = []
    VA = vertex(rels_gap, 1, 2); VB = vertex(rels_gap, 2, 3); VC = vertex(rels_gap, 3, 1)
    MA = modules3(VA[0], VA[1], VA[2], p); MB = modules3(VB[0], VB[1], VB[2], p); MC = modules3(VC[0], VC[1], VC[2], p)
    relC = relators2(VC[0], VC[1], VC[2])
    words = [w for L in range(1, 4) for w in itertools.product([1, 2], repeat=2 * L)]
    print("%s: #modules A,B,C = %d,%d,%d; words %d" % (label, len(MA), len(MB), len(MC), len(words))); sys.stdout.flush()
    for (ia, (P, Q)), (ib, (X0, Y0)), (ic, (Xc, Yc)) in itertools.product(enumerate(MA), enumerate(MB), enumerate(MC)):
        tag = "%s mods=(%d,%d,%d)" % (label, ia, ib, ic)
        if Q.charpoly() != X0.charpoly() or Y0.charpoly() != Xc.charpoly() or P.charpoly() != Yc.charpoly():
            continue
        order = sorted([r for r, m in Q.charpoly().roots(K)])
        if len(order) != 3: out.append((tag, "b has a repeated eigenvalue: not handled")); continue
        S = eigb(Q, K, order); S1 = eigb(X0, K, order)
        M = S1.inverse() * Y0 * S1; N = S.inverse() * P * S
        PR = PolynomialRing(K, 'h1,h2,g1,g2', order='degrevlex'); h1, h2, g1, g2 = PR.gens()
        H = diagonal_matrix(PR, [h1, h2, 1]); Hi = diagonal_matrix(PR, [g1, g2, 1])
        U = [None, H * M.change_ring(PR) * Hi, H * (M**2).change_ring(PR) * Hi]
        V = [None, N.change_ring(PR), (N**2).change_ring(PR)]; XP = [None, Xc, Xc**2]; YP = [None, Yc, Yc**2]
        gens = [h1 * g1 - 1, h2 * g2 - 1]
        for wd in words:
            Mw = identity_matrix(PR, 3); Tw = identity_matrix(K, 3)
            for s in range(0, len(wd), 2):
                Mw = Mw * U[wd[s]] * V[wd[s + 1]]; Tw = Tw * XP[wd[s]] * YP[wd[s + 1]]
            gens.append(Mw.trace() - Tw.trace())
        I = PR.ideal(gens)
        if list(I.groebner_basis()) == [1]: out.append((tag, "trace ideal (1)")); continue
        dim = I.dimension(); msg = "trace ideal NOT (1), dimension %d" % dim
        if dim == 0:
            ok = []
            for pt in I.variety():
                HL = diagonal_matrix(K, [pt[h1], pt[h2], 1]); u = HL * M * HL.inverse()
                good = True
                for r in relC:
                    R = identity_matrix(K, 3)
                    for l in r: R = R * {1: u, -1: u.inverse(), 2: N, -2: N.inverse()}[l]
                    good = good and R == 1
                ok.append(good)
            msg += ", F_p-points verified on relators of C: %s" % ok
        out.append((tag, msg))
    return out
if __name__ == "__main__":
    mode = sys.argv[1]; p = int(sys.argv[2]); assert is_prime(p) and p % 5460 == 1
    for stmt in ['F := FreeGroup("a", "b", "c")', 'a := F.1', 'b := F.2', 'c := F.3']:
        E(stmt)
    t0 = time.time()
    if mode == "cal":
        # calibration: a literal triple (x,y,z) of 3-elements of the Frobenius group 7:3 pairwise generating it; the
        # triangle with vertex relators of (x,y), (y,z), (z,x) has the 3-dim module of 7:3 as a vertex-faithful
        # representation, so a verified point must be found. (An A5 version does not exist: 3-elements of A5 are
        # 3-cycles, two generate A5 iff their supports meet in one point, and no three 3-subsets of a 5-set do.)
        rels = E("""function() local Fr, els, rs, t, rel;
            Fr := PrimitiveGroup(7, 3); rs := RandomSource(IsMersenneTwister, 20260913);
            els := Filtered(AsList(Fr), g -> Order(g) = 3);
            repeat t := List([1..3], i -> Random(rs, els));
            until ForAll([[1,2],[2,3],[3,1]], pr -> Size(Group(t{pr})) = 21);
            rel := function(pair, i, j) local FF; FF := Range(IsomorphismFpGroupByGenerators(Fr, pair));
                return List(RelatorsOfFpGroup(FF), w -> MappedWord(w, FreeGeneratorsOfFpGroup(FF), GeneratorsOfGroup(F){[i, j]})); end;
            return Concatenation(rel(t{[1,2]}, 1, 2), rel(t{[2,3]}, 2, 3), rel(t{[3,1]}, 3, 1)); end""")()
        res = analyse("CAL 7:3 literal triple", rels, p)
    else:
        libgap.Read("cckw334.g"); CCKW = E("CCKW"); res = []
        for G in CCKW:
            if str(G["name"]) in ("G_0^{14,26,40}", "G_4^{14,26,40}", "G_0^{18,26,40}"):
                res += analyse(str(G["name"]), G["rels"], p)
    for tag, msg in res: print(tag, "::", msg)
    print("CCKW_D3_DONE %.1fs" % (time.time() - t0))
