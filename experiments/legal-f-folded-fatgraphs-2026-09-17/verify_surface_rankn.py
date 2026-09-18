"""Rank-general independent checker for a legal f-folded fatgraph certificate.

Same fatgraph checks as verify_surface.py: rebuild the boundary from phi0, power and minus_words;
check the pairing; (L), (2), (3), (4); connectivity and chi < 0. The pairing may use only some
of the letters. The automorphism certificate works in any rank n:

  * an explicit inverse is checked by free reduction (default: greedy Nielsen reduction);
  * phi0 is positive, |det M| = 1, and M is primitive (its graph is strongly connected and has a
    loop);
  * chi_M (computed in exact integers by Faddeev--LeVerrier) is irreducible over Q. For n = 3
    (no root +-1) and n = 4 (no root +-1 and no factorisation into monic integer quadratics) this
    is decided by hand-written exact code; for every n it is also decided by sympy's exact
    factorisation over Z, and the two must agree;
  * for even n, chi_{M^2} is not palindromic. This excludes a mapping class of the orientable
    surface of genus n/2 with one boundary component (see the rank-n route).

usage: python3 verify_surface_rankn.py cert.json [inverse json]
"""
import sys, json
from math import isqrt
import verify_surface as V


def matmul(A, B):
    n = len(A)
    return [[sum(A[i][t] * B[t][j] for t in range(n)) for j in range(n)] for i in range(n)]


def charpoly(M):
    """Faddeev--LeVerrier in exact integers: coefficients [1, c1, ..., cn] of det(tI - M)."""
    n = len(M)
    I = [[int(i == j) for j in range(n)] for i in range(n)]
    c = [1]
    Mk = I
    for k in range(1, n + 1):
        AM = matmul(M, Mk)
        ck = -sum(AM[i][i] for i in range(n))
        assert ck % k == 0
        ck //= k
        c.append(ck)
        Mk = [[AM[i][j] + ck * I[i][j] for j in range(n)] for i in range(n)]
    return c


def ev(c, x):
    r = 0
    for a in c:
        r = r * x + a
    return r


def irreducible(c):
    n = len(c) - 1
    if any(ev(c, r) == 0 for r in (1, -1)):
        return False
    if n == 3:
        return abs(c[3]) == 1
    elif n == 4:
        a3, a2, a1, a0 = c[1], c[2], c[3], c[4]
        if abs(a0) != 1:
            return None
        for q in (1, -1):
            s = a0 // q
            # (t^2 + p t + q)(t^2 + r t + s): p + r = a3, pr + q + s = a2, ps + qr = a1
            prod = a2 - q - s
            disc = a3 * a3 - 4 * prod
            if disc < 0 or isqrt(disc) ** 2 != disc:
                continue
            for p in {(a3 + isqrt(disc)) // 2, (a3 - isqrt(disc)) // 2}:
                r = a3 - p
                if p + r == a3 and p * r == prod and p * s + q * r == a1:
                    return False
        return True
    return None


def irreducible_sympy(c):
    import sympy
    t = sympy.symbols("t")
    f = sum(a * t ** (len(c) - 1 - i) for i, a in enumerate(c))
    const, fl = sympy.factor_list(f, t)
    return abs(const) == 1 and len(fl) == 1 and fl[0][1] == 1 and sympy.degree(fl[0][0], t) == len(c) - 1


def primitive(M):
    """Strongly connected transition graph with a loop, so M is irreducible and aperiodic."""
    n = len(M)
    def reach(adj):
        seen, st = {0}, [0]
        while st:
            i = st.pop()
            for j in range(n):
                if adj(i, j) and j not in seen:
                    seen.add(j); st.append(j)
        return len(seen) == n
    return reach(lambda i, j: M[j][i] > 0) and reach(lambda i, j: M[i][j] > 0) and any(M[i][i] > 0 for i in range(n))


def main():
    cert = json.load(open(sys.argv[1]))
    phi0 = cert["phi0"]
    letters = "".join(sorted(phi0))
    n = len(letters)
    psi = json.loads(sys.argv[2]) if len(sys.argv) > 2 else V.nielsen_inverse(phi0)
    assert psi is not None, "no inverse found"
    for x in letters:
        assert V.red(V.app(phi0, V.app(psi, x))) == x and V.red(V.app(psi, V.app(phi0, x))) == x, ("inverse fails", x)
    assert all(set(v) <= set(letters) for v in phi0.values()), "phi0 not positive"
    M = [[phi0[col].count(row) for col in letters] for row in letters]
    cp = charpoly(M)
    assert abs(cp[-1]) == 1, "det not +-1"
    assert primitive(M), "not primitive"
    irr = irreducible(cp)
    irr_sympy = irreducible_sympy(cp)
    assert irr_sympy is True and irr in (True, None), ("charpoly not irreducible", cp, irr, irr_sympy)
    rep = {"automorphism": "explicit inverse verified", "rank": n, "charpoly": cp, "primitive": True,
           "irreducible": "hand-written exact and sympy" if irr else "sympy"}
    if n % 2 == 0:
        c2 = charpoly(matmul(M, M))
        assert c2 != c2[::-1], "charpoly of M^2 palindromic"
        rep["charpoly(M^2) not palindromic"] = True
    V_main_fatgraph(cert, rep)


def V_main_fatgraph(cert, rep):
    phi0, m, words, p = cert["phi0"], cert["power"], cert["minus_words"], cert["pairing"]
    letters = "".join(sorted(phi0))
    inv, red, app = V.inv, V.red, V.app
    phi = V.power(phi0, m)
    label, kind, fcorner_after, circles = [], [], [], []
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
                label.append(x); kind.append(side)
                fcorner_after.append(side == "+" and ((i + 1) % len(word)) in fstarts)
            circles.append((start, len(word)))
    N = len(label)
    nxt = [0] * N
    for s, L in circles:
        for i in range(L):
            nxt[s + i] = s + (i + 1) % L
    assert len(p) == N, "boundary reconstruction mismatch"
    assert all(p[p[d]] == d and p[d] != d for d in range(N)), "pairing not an involution"
    assert all(label[p[d]] == inv(label[d]) for d in range(N)), "labels not inverse"
    seen, verts = [False] * N, []
    for d in range(N):
        if not seen[d]:
            o, e = [], d
            while not seen[e]:
                seen[e] = True; o.append(e); e = nxt[p[e]]
            verts.append(o)
    vid = {d: i for i, o in enumerate(verts) for d in o}
    g = V.gates(phi, letters)
    for o in verts:
        labs = [g[label[d]] for d in o]
        assert len(set(labs)) == len(labs), ("(L) fails", [label[d] for d in o])
        assert len(o) >= 2
    fcount = [0] * len(verts); mcount = [0] * len(verts)
    for q in range(N):
        v = vid[nxt[q]]
        fcount[v] += fcorner_after[q]
        mcount[v] += kind[q] == "-"
    for i, o in enumerate(verts):
        assert fcount[i] <= 1, "(3) fails"
        assert fcount[i] == 0 or len(o) == 2, "(2) fails"
        assert mcount[i] <= 1, "(4) vertex fails"
    assert all(not (kind[d] == "-" and kind[p[d]] == "-") for d in range(N)), "(4) edge fails"
    par = list(range(N))
    def find(x):
        while par[x] != x:
            par[x] = par[par[x]]; x = par[x]
        return x
    for d in range(N):
        for e in (p[d], nxt[p[d]]):
            par[find(d)] = find(e)
    comps = len({find(d) for d in range(N)})
    Vn, E = len(verts), N // 2
    chi = Vn - E
    rep.update({"darts": N, "V": Vn, "E": E, "chi(X)": chi, "components": comps,
                "valences": sorted(len(o) for o in verts),
                "gates": "".join(g[d] for d in letters + letters.upper())})
    assert comps == 1 and chi < 0
    rep["genus of S*_f(X)"] = 1 - chi // 2
    print("CERTIFICATE OK", json.dumps(rep))


if __name__ == "__main__":
    main()
