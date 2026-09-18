"""Lemma 8: one-endedness of D(F_2, C) through a one-relator presentation.

Lemma 8 of research/malnormal-free-doubles-surface-certificates-proof.md.  Suppose C = <y, c> where
y is primitive in F_2, and let phi, phi' be automorphisms of F_2 with phi(y) = phi'(y) = b.  Then
    D(F_2, C) = < a, b, e | r >,   r = phi(c)(a, b) . phi'(c)(e, b)^-1,
a one-relator group.  If the Whitehead graph of the cyclic reduction of r (vertices a, A, b, B, e, E)
is connected with no cut vertex, then r lies in no proper free factor of F(a, b, e) (Whitehead's
cut-vertex lemma), so D is freely indecomposable (Shenitzer), hence one-ended (Stallings).

The script enumerates bases (y, c) of C obtained from (c1, c2) by Nielsen moves up to depth DEPTH,
tests y for primitivity by greedy Whitehead reduction in F_2 (length 1 means primitive), and checks
phi(y) = b and the Whitehead graph directly.  The two copies of F_2 may use different automorphisms
with phi(y) = b; the script composes phi with a -> b^i a^{+-1} b^j, |i|, |j| <= SHIFT, on each side.
Every certificate is re-checked by check(): <y, c> and <g1, g2> have the same Stallings graph
(mutual membership), phi(a), phi(b) generate F_2 (their Stallings graph is the rose), phi(y) =
phi'(y) = b, r is recomputed from phi(c) and phi'(c), and the Whitehead graph test is rerun.
Usage: python3 one_ended_primitive.py g1 g2 [g1 g2 ...]
"""
import sys

LET = "aAbBeE"
DEPTH = 4
SHIFT = 3


def w_of(s):
    return [LET.index(ch) for ch in s]


def s_of(w):
    return "".join(LET[x] for x in w)


def inv(w):
    return [x ^ 1 for x in reversed(w)]


def red(w):
    out = []
    for x in w:
        if out and out[-1] == x ^ 1:
            out.pop()
        else:
            out.append(x)
    return out


def cyc(w):
    w = red(w)
    while len(w) >= 2 and w[0] == w[-1] ^ 1:
        w = w[1:-1]
    return w


def apply(phi, w):
    """phi = (image of a, image of b) as letter lists; returns reduced phi(w)."""
    out = []
    for x in w:
        img = phi[x >> 1]
        out.extend(img if x % 2 == 0 else inv(img))
    return red(out)


def compose(psi, phi):
    """psi o phi."""
    return (apply(psi, phi[0]), apply(psi, phi[1]))


def whitehead_autos():
    """Elementary Whitehead automorphisms of F_2 and their inverses (a -> ab^{+-1}, a -> b^{+-1}a, ...)."""
    autos = []
    for x in (0, 2):
        y = 2 - x
        for s in (y, y ^ 1):
            for side in ("right", "left"):
                img = [x, s] if side == "right" else [s, x]
                phi = [None, None]
                phi[x >> 1] = img
                phi[y >> 1] = [y]
                autos.append(tuple(phi))
    return autos


AUTOS = whitehead_autos()


def primitive_map(y):
    """Return phi with phi(y) = b (as a reduced word) if y is primitive in F_2, else None."""
    phi = ([0], [2])
    w = cyc(y)
    while len(w) > 1:
        best = None
        for au in AUTOS:
            w2 = cyc(apply(au, w))
            if len(w2) < len(w) and (best is None or len(w2) < len(best[0])):
                best = (w2, au)
        if best is None:
            return None
        w, au = best
        phi = compose(au, phi)
    if not w:
        return None
    img = apply(phi, y)  # = g x g^-1 for a letter x
    k = (len(img) - 1) // 2
    g = img[:k]
    assert red(g + [img[k]] + inv(g)) == img
    conj = (red(inv(g) + [0] + g), red(inv(g) + [2] + g))
    phi = compose(conj, phi)
    x = apply(phi, y)
    assert len(x) == 1
    swap = {0: ([2], [0]), 1: ([3], [0]), 2: ([0], [2]), 3: ([0], [3])}[x[0]]
    phi = compose(swap, phi)
    assert apply(phi, y) == [2]
    # phi is an automorphism: it is a composite of Whitehead automorphisms, an inner map and a
    # permutation/inversion of letters.
    return phi


def whitehead_ok(r):
    """Whitehead graph of the cyclic word r on 6 vertices: connected and without cut vertex."""
    n = len(r)
    edges = [(r[i], r[(i + 1) % n] ^ 1) for i in range(n)]

    def connected(removed):
        verts = [v for v in range(6) if v != removed]
        seen = {verts[0]}
        stack = [verts[0]]
        while stack:
            v = stack.pop()
            for p, q in edges:
                for s, t in ((p, q), (q, p)):
                    if s == v and t != removed and t not in seen:
                        seen.add(t)
                        stack.append(t)
        return len(seen) == len(verts)

    return connected(None) and all(connected(v) for v in range(6))


def nielsen_bases(c1, c2, depth):
    seen = {(tuple(c1), tuple(c2))}
    frontier = [(c1, c2)]
    for _ in range(depth):
        nxt = []
        for u, v in frontier:
            for p, q in ((red(u + v), v), (red(u + inv(v)), v), (red(v + u), v), (red(inv(v) + u), v),
                         (u, red(v + u)), (u, red(v + inv(u))), (u, red(u + v)), (u, red(inv(u) + v)),
                         (v, u), (inv(u), v)):
                key = (tuple(p), tuple(q))
                if key not in seen:
                    seen.add(key)
                    nxt.append((p, q))
        frontier = nxt
    return [(list(p), list(q)) for p, q in seen]


def certify(g1, g2):
    for y, c in nielsen_bases(w_of(g1), w_of(g2), DEPTH):
        phi = primitive_map(y)
        if phi is None:
            continue
        # the two copies of F_2 may use different automorphisms fixing b: a -> b^i a^{+-1} b^j
        images = []
        for i in range(-SHIFT, SHIFT + 1):
            for j in range(-SHIFT, SHIFT + 1):
                for x in (0, 1):
                    psi = (red(power(2, i) + [x] + power(2, j)), [2])
                    chi = compose(psi, phi)
                    images.append((chi, apply(chi, c)))
        for chi, pc in images:
            for chi2, pc2 in images:
                pc_e = [4 if x == 0 else 5 if x == 1 else x for x in pc2]
                r = cyc(pc + inv(pc_e))
                if r and whitehead_ok(r):
                    return y, c, chi, chi2, r
    return None


def fold(gens):
    """Stallings graph of <gens> in F(a, b): dict vertex -> {letter: vertex}, base 0."""
    edges, nv = [], 1
    for g in gens:
        v = 0
        for i, x in enumerate(g):
            u = 0 if i == len(g) - 1 else nv
            nv += u == nv
            edges.append((v, x, u))
            v = u
    parent = list(range(nv))

    def find(x):
        while parent[x] != x:
            x = parent[x]
        return x

    while True:
        out, merged = {}, False
        for v, x, u in edges:
            for key, tgt in (((find(v), x), find(u)), ((find(u), x ^ 1), find(v))):
                if key in out and find(out[key]) != find(tgt):
                    parent[find(tgt)] = find(out[key])
                    merged = True
                out.setdefault(key, tgt)
        if not merged:
            break
    G = {}
    for v, x, u in edges:
        G.setdefault(find(v), {})[x] = find(u)
        G.setdefault(find(u), {})[x ^ 1] = find(v)
    return G, find(0)


def member(G, base, w):
    v = base
    for x in w:
        if x not in G.get(v, {}):
            return False
        v = G[v][x]
    return v == base


def check(g1, g2, res):
    """Independent re-check of a Lemma 8 certificate (y, c, phi, phi', r)."""
    y, c, chi, chi2, r = res
    C1, C2 = w_of(g1), w_of(g2)
    G, o = fold([C1, C2])
    B, p = fold([y, c])
    same = all(member(G, o, w) for w in (y, c)) and all(member(B, p, w) for w in (C1, C2))
    roses = [fold(list(ch)) for ch in (chi, chi2)]
    autos = all(len(R) == 1 and len(R[o2]) == 4 for R, o2 in roses)  # image generates F_2
    fixes = apply(chi, y) == [2] and apply(chi2, y) == [2]
    rel = cyc(apply(chi, c) + inv([4 if x == 0 else 5 if x == 1 else x for x in apply(chi2, c)])) == r
    return same and autos and fixes and rel and whitehead_ok(r)


def power(x, k):
    return [x] * k if k >= 0 else [x ^ 1] * (-k)


if __name__ == "__main__":
    args = sys.argv[1:]
    done = 0
    for i in range(0, len(args), 2):
        res = certify(args[i], args[i + 1])
        if res is None:
            print(args[i], args[i + 1], "=> undecided", flush=True)
            continue
        assert check(args[i], args[i + 1], res), "certificate failed the independent re-check"
        done += 1
        y, c, chi, chi2, r = res
        print(args[i], args[i + 1], "=> ONE-ENDED  y=%s c=%s phi=(%s,%s) phi'=(%s,%s) r=%s  [re-checked]"
              % (s_of(y), s_of(c), s_of(chi[0]), s_of(chi[1]), s_of(chi2[0]), s_of(chi2[1]), s_of(r)),
              flush=True)
    print("one-ended certified for", done, "/", len(args) // 2)
