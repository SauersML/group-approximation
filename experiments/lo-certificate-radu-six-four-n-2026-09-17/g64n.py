"""Reconstruct Radu's torsion-free (6,4n)-group Gamma_{6,4n} (arXiv:1712.01091, Prop. 6.x) from
the local permutations printed in its proof, trying all sign/inverse conventions, and keep the
conventions that give a consistent complete VH datum containing Gamma_{4,4}'s four squares."""
import itertools, sys
from bmw import BMW, RADU_44, parse_word

def cyc(perm, *cycles):
    for c in cycles:
        for i, x in enumerate(c):
            perm[x] = c[(i + 1) % len(c)]
    return perm

def radu_perms(n, corrected=False):
    """corrected=True replaces the printed b_3 permutation (a1 a3 a1^-1)(a2 a2^-1 a3^-1) by (a1 a3 a1^-1)."""
    A = [1, 2, 3]; B = list(range(1, 2 * n + 1))
    P = {}  # b_j (positive) -> permutation of a-letters (+-i)
    ident = lambda letters: {x: x for i in letters for x in (i, -i)}
    P[1] = cyc(ident(A), (1, 2), (-1, -2))
    P[2] = cyc(ident(A), (1, 2, -1, -2))
    P[3] = cyc(ident(A), (1, 3, -1)) if corrected else cyc(ident(A), (1, 3, -1), (2, -2, -3))
    for j in range(2, n):
        P[2 * j] = cyc(ident(A), (1, -1, -3), (2, 3, -2))
        P[2 * j + 1] = cyc(ident(A), (1, 3, -1), (2, -2, -3))
    P[2 * n] = cyc(ident(A), (1, -1, -3))
    S = {}
    S[1] = cyc(ident(B), (1, -1, -2), *[(2 * k - 1, 2 * k) for k in range(2, n + 1)], *[(-(2 * k - 1), -2 * k) for k in range(2, n + 1)])
    S[2] = cyc(ident(B), (1, 2, -1), (3, -3), (2 * n, -2 * n), *[(2 * k, 2 * k + 1) for k in range(2, n)], *[(-2 * k, -(2 * k + 1)) for k in range(2, n)])
    S[3] = cyc(ident(B), tuple(range(2 * n, 0, -1)), tuple(-x for x in range(2 * n, 0, -1)))
    return P, S

def invp(p): return {v: k for k, v in p.items()}
def conj(p): return {-k: -v for k, v in p.items()}

def fmt(t, x): return "%s%d%s" % (t, abs(x), "^-1" if x < 0 else "")

def attempt(n, cP, cS, corrected=False):
    P, S = radu_perms(n, corrected)
    def tr(p, c):
        if c[0]: p = invp(p)
        if c[1]: p = conj(p)
        return p
    P = {k: tr(v, cP) for k, v in P.items()}
    S = {k: tr(v, cS) for k, v in S.items()}
    # corners with positive v: b_v a_u = a_u' b_v'.  u' = P[v](u).  v' from S with index (u or u', variant cS[2])
    rels = set()
    for v in P:
        for u in [x for i in (1, 2, 3) for x in (i, -i)]:
            u2 = P[v][u]
            key = [u, u2, -u, -u2][cS[2] + 2 * cS[3]]
            if abs(key) not in S: return None
            s = S[abs(key)] if key > 0 else invp(S[-key])
            v2 = s[v]
            # relator v u v2^-1 u2^-1
            rels.add((("b", v), ("a", u), ("b", -v2), ("a", -u2)))
    try:
        rel_strs = []
        for r in rels:
            # rotate to start with an a-letter
            r = r[1:] + r[:1]
            rel_strs.append(" ".join(fmt(t, x) for t, x in r))
        G = BMW(3, 2 * n, rel_strs)
    except AssertionError:
        return None
    H = BMW(2, 2, RADU_44)
    ok = all(G.swap.get(k) == val for k, val in H.swap.items())
    return (G, rel_strs) if ok else None

if __name__ == "__main__":
    n = int(sys.argv[1])
    corrected = len(sys.argv) > 2 and sys.argv[2] == "corrected"
    found = []
    for cP in itertools.product((0, 1), repeat=2):
        for cS in itertools.product((0, 1), repeat=4):
            r = attempt(n, cP, cS, corrected)
            if r: found.append((cP, cS, r))
    print("n=%d conventions giving a valid datum containing Gamma_44:" % n, [(a, b) for a, b, _ in found])
    swaps = {tuple(sorted(r[0].swap.items())) for _, _, r in found}
    print("distinct data:", len(swaps))
    if found:
        G, rels = found[0][2]
        print("torsion-free (no square of form (xy)^2):", all(not (r.split()[0] == r.split()[2] and r.split()[1] == r.split()[3]) for r in rels))
