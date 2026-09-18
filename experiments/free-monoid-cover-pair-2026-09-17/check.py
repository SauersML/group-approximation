"""Finite checks for the free-monoid calibration of
research/cover-pair-sections-force-fixed-point-surjectivity.md.

M = {a,b}*, alphabet {0,1}, (m*x)(w) = x(mw), automata tau(x)(w) = mu((x(ws))_s).
Pair: X = {x : x(wb) = 0 for all w}, F(x)(w) = x(wa), Phi = {a}.

Checks, on the ball B_n of words of length <= n:
 (1) the lift x' of z (x'(wa)=z(w), x'(wb)=0, x'(eps)=x(eps)) lies in X, has F(x')=z on B_{n-1},
     and differs from x only on Delta(F(x),z).a  (exhaustive over x in X|B_n, z on B_{n-1});
 (2) the only constants of {0,1}^M lying in X are 0^M, and F(0^M) = 0^M, so 1^M has no constant preimage;
 (3) Rees-periodicity: for random automata with memory {eps,a,b}, tau maps Per_n (x constant on words
     of length > n) into Per_n, and injectivity on Per_n implies bijectivity (finite set).
"""
import itertools, random

def ball(n):
    out = [""]
    for k in range(1, n + 1):
        out += ["".join(t) for t in itertools.product("ab", repeat=k)]
    return out

def check_lift(n):
    B, Bm = ball(n), ball(n - 1)
    free = [w for w in B if not w.endswith("b")]          # eps and words ending in a
    cnt = 0
    for bits in itertools.product((0, 1), repeat=len(free)):
        x = {w: 0 for w in B}
        x.update(dict(zip(free, bits)))
        Fx = {w: x[w + "a"] for w in Bm}
        for zb in itertools.product((0, 1), repeat=len(Bm)):
            z = dict(zip(Bm, zb))
            xp = {"": x[""]}
            for w in Bm:
                xp[w + "a"] = z[w]
                xp[w + "b"] = 0
            assert all(xp[w] == 0 for w in B if w.endswith("b"))            # x' in X
            assert all(xp[w + "a"] == z[w] for w in Bm)                     # F(x') = z
            diff = {w for w in B if xp[w] != x[w]}
            allowed = {w + "a" for w in Bm if z[w] != Fx[w]}
            assert diff <= allowed                                          # Delta in Delta.Phi
            cnt += 1
    return cnt

def check_constants(n):
    B = ball(n)
    consts_in_X = [c for c in (0, 1) if all(c == 0 for w in B if w.endswith("b"))]
    assert consts_in_X == [0]
    return consts_in_X

def per_points(n, rng=None):
    B = ball(n)
    for bits in itertools.product((0, 1), repeat=len(B) + 1):
        yield dict(zip(B, bits[:-1])), bits[-1]     # values on B_n, tail value

def apply(mu, x, tail, n):
    val = lambda w: x[w] if len(w) <= n else tail
    y = {w: mu[(val(w), val(w + "a"), val(w + "b"))] for w in ball(n)}
    ytail = mu[(tail, tail, tail)]
    return y, ytail

def check_rees(n, trials=200, seed=1):
    rng = random.Random(seed)
    keys = list(itertools.product((0, 1), repeat=3))
    inj = 0
    for _ in range(trials):
        mu = {k: rng.randint(0, 1) for k in keys}
        imgs = set()
        pts = list(per_points(n))
        for x, t in pts:
            y, yt = apply(mu, x, t, n)
            imgs.add((tuple(sorted(y.items())), yt))
        if len(imgs) == len(pts):
            inj += 1                       # injective on the finite set => bijective on it
    return inj

if __name__ == "__main__":
    for n in (1, 2, 3):
        print("n=%d lift cases checked: %d" % (n, check_lift(n)))
    print("constants in X:", check_constants(4))
    print("random automata injective (hence bijective) on Per_2:", check_rees(2))
    print("OK")
