"""Exact check of the bimodule identities in Lemma 1 of
research/artifacts/dihedral-cantor-k1-exponent-four-2026-09-16.md on finite models.

A = F_2^Y ⋊ D_n with Y = Z/n, r: y -> y+1, s: y -> -y; A' = span{e_y δ_{r^k}}, v = δ_s.
Elements of A ⊗_{A'} A are pairs (p, q) meaning p⊗1 + q⊗v (left A-basis {1⊗1, 1⊗v}).
Checks, for random b in A: (i) ω b = θ(b) ω with ω = 1⊗v + v⊗1, θ = Ad(v);
(ii) μ(a ω) = 0, and every kernel element (q v, q) of μ(p⊗1 + q⊗v) = p + q v equals q ω."""
import random, itertools
def run(n, trials=200):
    G = [(k, e) for e in (0, 1) for k in range(n)]          # r^k s^e
    def gmul(g, h):
        (k, e), (l, f) = g, h
        return ((k + (l if e == 0 else -l)) % n, e ^ f)
    def act(g, y):                                           # (r^k s^e) y
        k, e = g
        return ((y if e == 0 else -y) + k) % n
    def mul(x, z):                                           # x,z: sets of (y,g) = e_y δ_g
        out = set()
        for (y, g) in x:
            for (w, h) in z:
                if act(g, w) == y:                           # e_y δ_g e_w δ_h = [y = g w] e_y δ_{gh}
                    out ^= {(y, gmul(g, h))}
        return out
    add = lambda a, b: a ^ b
    one = {(y, (0, 0)) for y in range(n)}
    v = {(y, (0, 1)) for y in range(n)}
    basis = [(y, g) for y in range(n) for g in G]
    rnd = lambda: {t for t in basis if random.random() < 0.5}
    split = lambda b: ({t for t in b if t[1][1] == 0}, mul({t for t in b if t[1][1] == 1}, v))  # b = b0 + b1 v
    sig = lambda a: mul(mul(v, a), v)
    def rmul(pq, b):                                          # (p,q)·b = (p b0 + q σ(b1), p b1 + q σ(b0))
        p, q = pq; b0, b1 = split(b)
        return (add(mul(p, b0), mul(q, sig(b1))), add(mul(p, b1), mul(q, sig(b0))))
    def lmul(b, pq):
        return (mul(b, pq[0]), mul(b, pq[1]))
    omega = (v, one)
    for _ in range(trials):
        b = rnd()
        assert split(b)[0] | mul(split(b)[1], v) == b or add(split(b)[0], mul(split(b)[1], v)) == b
        assert rmul(omega, b) == lmul(sig(b), omega), "omega b != theta(b) omega"
        a = rnd()
        p, q = lmul(a, omega)
        assert add(p, mul(q, v)) == set(), "mu(a omega) != 0"
    # kernel of mu: (p, q) with p = q v; it is {q ω}: q ω = (q v, q)
    for _ in range(trials):
        q = rnd(); p = mul(q, v)
        assert lmul(q, omega) == (p, q)
    return True
for n in (3, 4, 5, 6, 8):
    random.seed(n)
    print(n, run(n))
