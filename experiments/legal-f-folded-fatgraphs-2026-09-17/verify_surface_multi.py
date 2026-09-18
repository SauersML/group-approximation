"""Independent checker for a legal f-folded fatgraph certificate (no import of ffold/sat4).

VARIANT verify_surface_multi.py: identical checks, except that X may be disconnected; what is
required is that the closed surface S*_f(X) (X with each d^- circle w glued to its d^+ circle
f(w)^{-1}) is connected and chi(X) < 0.  Step 5 of legal-f-folded-fatgraphs-give-surface-subgroups-proof
(pi_1-injectivity component by component, chi(S*_f(X)) = chi(X)) does not use connectivity of X.

Input: a JSON file with keys phi0, power, minus_words, pairing (as written by find_surface.py).
Everything else is rebuilt here from those four fields:

  * boundary: for each d^- word w = x_1..x_L, a d^- circle reading w and a d^+ circle reading
    f(w)^{-1} = f(x_L)^{-1} ... f(x_1)^{-1}; darts numbered circle by circle in that order;
  * fatgraph: edge involution p = pairing, face permutation nxt (boundary order), vertex
    permutation sigma = nxt o p (outgoing darts at a vertex); faces of (sigma, p) are the circles;
  * checks: p fixed-point-free involution with inverse labels; every boundary word cyclically
    reduced; (L) outgoing labels at every vertex in pairwise distinct gates; (2) f-vertices
    2-valent; (3) at most one f-corner per vertex; (4) no edge with d^- on both sides and at most
    one d^- corner per vertex; X connected; chi(X) = V - E;
  * the automorphism certificate for phi0: explicit inverse checked by free reduction, transition
    matrix determinant, primitivity (some power > 0), integer characteristic polynomial with no
    rational root (a cubic), i.e. the hypotheses of Step 7 of
    positive-f-folded-fatgraphs-have-only-even-valence-proof.

usage: python3 verify_surface.py cert.json [inverse json]   (default: inverse found by Nielsen reduction)
"""
import sys, json
from fractions import Fraction


def inv(x):
    return x.swapcase()


def red(w):
    out = []
    for x in w:
        if out and out[-1] == inv(x):
            out.pop()
        else:
            out.append(x)
    return "".join(out)


def app(phi, w):
    return "".join(phi[x] if x.islower() else red(phi[x.lower()][::-1].swapcase()) for x in w)


def power(phi, m):
    r = {x: x for x in phi}
    for _ in range(m):
        r = {x: red(app(phi, r[x])) for x in phi}
    return r


def gates(phi, letters):
    def D(d):
        return phi[d][0] if d.islower() else inv(phi[d.lower()][-1])
    dirs = letters + letters.upper()
    orb = {}
    for d in dirs:
        seq, e = [], d
        for _ in range(4 * len(dirs)):
            seq.append(e)
            e = D(e)
        orb[d] = seq
    same = lambda d, e: any(orb[d][j] == orb[e][j] for j in range(4 * len(dirs)))
    rep = {}
    for d in dirs:
        rep[d] = next(e for e in dirs if same(d, e))
    return rep


def charpoly3(M):
    tr = sum(M[i][i] for i in range(3))
    c2 = sum(M[i][i] * M[j][j] - M[i][j] * M[j][i] for i in range(3) for j in range(i + 1, 3))
    det = (M[0][0] * (M[1][1] * M[2][2] - M[1][2] * M[2][1]) - M[0][1] * (M[1][0] * M[2][2] - M[1][2] * M[2][0])
           + M[0][2] * (M[1][0] * M[2][1] - M[1][1] * M[2][0]))
    return [1, -tr, c2, -det]  # t^3 - tr t^2 + c2 t - det


def nielsen_inverse(phi):
    """Length-decreasing Nielsen moves on (phi(x_1), ..., phi(x_n)), tracking expressions.
    Returns psi with phi(psi(x)) = x, or None if the greedy reduction stalls (then no claim)."""
    letters = sorted(phi)
    u = [phi[x] for x in letters]
    e = [x for x in letters]
    iw = lambda w: w[::-1].swapcase()
    progress = True
    while progress and sum(map(len, u)) > len(u):
        progress = False
        for i in range(len(u)):
            for j in range(len(u)):
                if i == j:
                    continue
                for s in (0, 1):
                    uj, ej = (u[j], e[j]) if s == 0 else (iw(u[j]), iw(e[j]))
                    for left in (0, 1):
                        nu = red(uj + u[i]) if left else red(u[i] + uj)
                        if len(nu) < len(u[i]):
                            u[i] = nu; e[i] = red(ej + e[i]) if left else red(e[i] + ej)
                            progress = True
    if sum(map(len, u)) != len(u):
        return None
    psi = {}
    for w, ex in zip(u, e):
        if w.islower():
            psi[w] = ex
        else:
            psi[w.lower()] = iw(ex)
    return psi if sorted(psi) == letters else None


def main():
    cert = json.load(open(sys.argv[1]))
    psi = json.loads(sys.argv[2]) if len(sys.argv) > 2 else nielsen_inverse(cert["phi0"])
    assert psi is not None, "no inverse found"
    phi0, m, words, p = cert["phi0"], cert["power"], cert["minus_words"], cert["pairing"]
    letters = "".join(sorted(phi0))
    rep = {}
    # automorphism certificate
    for x in letters:
        assert red(app(phi0, app(psi, x))) == x and red(app(psi, app(phi0, x))) == x, ("inverse fails", x)
    assert all(set(v) <= set(letters) for v in phi0.values()), "phi0 not positive"
    M = [[phi0[col].count(row) for col in letters] for row in letters]
    cp = charpoly3(M)
    assert abs(cp[3]) == 1, "det not +-1"
    rational_roots = [r for r in (1, -1) if sum(c * r ** (3 - i) for i, c in enumerate(cp)) == 0]
    assert not rational_roots, "charpoly has a rational root"
    P, k = M, 1
    while not all(v > 0 for row in P for v in row):
        P = [[sum(P[i][t] * M[t][j] for t in range(3)) for j in range(3)] for i in range(3)]
        k += 1
        assert k < 20, "not primitive"
    rep["automorphism"] = "explicit inverse verified"
    rep["charpoly"] = cp
    rep["M^k>0 at k"] = k
    # boundary
    phi = power(phi0, m)
    label, kind, circ, fcorner_after = [], [], [], []
    circles = []
    for w in words:
        for side in "-+":
            start = len(label)
            if side == "-":
                word, fstarts = w, set()
            else:
                blocks = [red(app(phi, x))[::-1].swapcase() for x in reversed(w)]
                word, fstarts, pos = "".join(blocks), set(), 0
                for b in blocks:
                    fstarts.add(pos); pos += len(b)
            ww = word + word
            assert red(ww) == ww and word[0] != inv(word[-1]), ("boundary word not cyclically reduced", word)
            for i, x in enumerate(word):
                label.append(x); kind.append(side); circ.append(len(circles))
                # corner after dart i is a junction corner iff dart i+1 (cyclically) starts a block
                fcorner_after.append(side == "+" and ((i + 1) % len(word)) in fstarts)
            circles.append((start, len(word)))
    N = len(label)
    nxt = [0] * N
    for s, L in circles:
        for i in range(L):
            nxt[s + i] = s + (i + 1) % L
    assert label == cert["labels"] and len(p) == N, "boundary reconstruction mismatch"
    assert all(p[p[d]] == d and p[d] != d for d in range(N)), "pairing not an involution"
    assert all(label[p[d]] == inv(label[d]) for d in range(N)), "labels not inverse"
    # vertices: sigma = nxt o p on outgoing darts; the corner (q, nxt q) sits at the vertex of nxt q
    seen, verts = [False] * N, []
    for d in range(N):
        if not seen[d]:
            o, e = [], d
            while not seen[e]:
                seen[e] = True; o.append(e); e = nxt[p[e]]
            verts.append(o)
    vid = {d: i for i, o in enumerate(verts) for d in o}
    g = gates(phi, letters)
    for o in verts:
        labs = [g[label[d]] for d in o]
        assert len(set(labs)) == len(labs), ("(L) fails", [label[d] for d in o])
        assert len(o) >= 2
    fcount = [0] * len(verts); mcount = [0] * len(verts)
    for q in range(N):
        v = vid[nxt[q]]  # corner (q, nxt q)
        fcount[v] += fcorner_after[q]
        mcount[v] += kind[q] == "-"
    for i, o in enumerate(verts):
        assert fcount[i] <= 1, "(3) fails"
        assert fcount[i] == 0 or len(o) == 2, "(2) fails"
        assert mcount[i] <= 1, "(4) vertex fails"
    assert all(not (kind[d] == "-" and kind[p[d]] == "-") for d in range(N)), "(4) edge fails"
    # connectivity of X: union darts along p and sigma
    par = list(range(N))
    def find(x):
        while par[x] != x:
            par[x] = par[par[x]]; x = par[x]
        return x
    for d in range(N):
        for e in (p[d], nxt[p[d]]):
            par[find(d)] = find(e)
    comps_X = len({find(d) for d in range(N)})
    for ci in range(0, len(circles), 2):          # glue d^- circle ci to d^+ circle ci+1
        par[find(circles[ci][0])] = find(circles[ci + 1][0])
    comps = len({find(d) for d in range(N)})
    rep["components of X"] = comps_X
    V, E = len(verts), N // 2
    chi = V - E
    rep.update({"darts": N, "V": V, "E": E, "chi(X)": chi, 
                "valences": sorted(len(o) for o in verts), "components of S*": comps, "gates": "".join(g[d] for d in letters + letters.upper()),
                "f-corners": sum(fcorner_after)})
    assert comps == 1 and chi < 0
    rep["genus of S*_f(X)"] = 1 - chi // 2
    print("CERTIFICATE OK", json.dumps(rep))


if __name__ == "__main__":
    main()
