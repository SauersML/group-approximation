"""Finite-model check of Step 4 of v-times-ample-full-groups-are-generated-by-transpositions-proof.

Model: H = pair groupoid on a finite set Q = {0..m-1} (ample, Hausdorff, discrete unit space).
An element h of F(G_V x H) in normal form with singleton Q_i is a list of pieces
(u, x, v, y): [u] x {x} -> [v] x {y} by prefix replacement u->v, x->y.
Sources must partition Omega (for each x the u's form a complete prefix code) and so must ranges.
We build random such h, form rho, rho' as in Step 4, and test rho' h rho^{-1} = h^(0) h^(1)
on random points (long finite words stand in for infinite words; all prefixes used are short).
Evidence only: the proof in the route is the certificate.
"""
import random, sys

def random_prefix_code(k, rng):
    code = [""]
    while len(code) < k:
        w = code.pop(rng.randrange(len(code)))
        code += [w + "0", w + "1"]
    return code

def random_element(m, rng, maxk=6):
    ns = [rng.randint(1, maxk) for _ in range(m)]
    total = sum(ns)
    # split total into m positive parts for ranges
    cuts = sorted(rng.sample(range(1, total), m - 1)) if m > 1 else []
    parts = [b - a for a, b in zip([0] + cuts, cuts + [total])]
    src = [(u, x) for x in range(m) for u in random_prefix_code(ns[x], rng)]
    rng_ = [(v, y) for y in range(m) for v in random_prefix_code(parts[y], rng)]
    rng.shuffle(rng_)
    return [(u, x, v, y) for (u, x), (v, y) in zip(src, rng_)]

def apply(pieces, pt):
    s, x = pt
    hits = [(u, xx, v, y) for (u, xx, v, y) in pieces if xx == x and s.startswith(u)]
    assert len(hits) == 1, ("not a partition", pt, hits)
    u, _, v, y = hits[0]
    return (v + s[len(u):], y)

def inverse(pieces):
    return [(v, y, u, x) for (u, x, v, y) in pieces]

def rho_of(pieces, use_range):
    out = []
    for (u, x, v, y) in pieces:
        w, q = (v, y) if use_range else (u, x)
        for a in "01":
            out.append((w + a, q, a + w, q))
    return out

def copy_apply(h, pt):  # h^(0) h^(1): acts as h on each half
    s, x = pt
    t, y = apply(h, (s[1:], x))
    return (s[0] + t, y)

def main(trials=300, pts=200, seed=20260916):
    rng = random.Random(seed)
    for t in range(trials):
        m = rng.randint(1, 4)
        h = random_element(m, rng)
        rho, rhop = rho_of(h, False), rho_of(h, True)
        rho_inv = inverse(rho)
        for _ in range(pts):
            s = "".join(rng.choice("01") for _ in range(40))
            x = rng.randrange(m)
            lhs = apply(rhop, apply(h, apply(rho_inv, (s, x))))
            rhs = copy_apply(h, (s, x))
            # compare on the common finite window (lengths may differ by prefix bookkeeping)
            L = min(len(lhs[0]), len(rhs[0]))
            if lhs[1] != rhs[1] or lhs[0][:L] != rhs[0][:L] or len(lhs[0]) != len(rhs[0]):
                print("FAIL", t, h, (s, x), lhs, rhs); sys.exit(1)
    print(f"OK: {trials} random normal-form elements, {pts} points each; rho' h rho^-1 = h^(0) h^(1)")

if __name__ == "__main__":
    main()
