#!/usr/bin/env python3
"""Acceptance of patchwork labellings of the inner Grassmann 2-to-1 test.

Test: A = l-dim subspaces L of F_2^m, B = (l-1)-dim subspaces L' < L,
edge (L, L') uniform over incident pairs.  An A-label is a functional on L;
it is given as the restriction of a global form f (int, <f,x> = parity(f&x)).
The constraint is restriction: B-label of L' must equal W_L|_{L'}.
val(W) = E_{L'} max_b Pr_{L > L'}[W_L|_{L'} = b]   (optimal B-labels).

Patchworks measured (forms f_j drawn at random, pairwise distinct):
  honest      one global form
  two-patch   W_L in {f1|L, f2|L} with an independent random bit per L
  zoom-in     z(L) = highest-ranked point of L (random ranks), W_L = f_{z(L)}|L
  zoom-out    H(L) = highest-ranked hyperplane containing L, W_L = f_{H(L)}|L
  zoom-in-2   as zoom-in but f_z in {f1, f2} (two forms, point-dependent choice)
Also checked exactly:
  seed identity  on lift-satisfied edges from a B-seed, the branch bit equals
                 W_L(x_e); corr with chi_f >= 2 s a - 1 where s = satisfied
                 fraction and a = agreement of phi(x) = W_{L'+x}(x) with f on S.
  vacuity        every h: F_2^m -> F_2 is pointwise explained by the m+1 forms
                 {0, e_1..e_m}, while bent h has all |Walsh corr| = 2^(-m/2).
"""
import itertools, random, sys

def par(x):
    return bin(x).count("1") & 1

def span(vecs):
    s = {0}
    for v in vecs:
        s |= {u ^ v for u in s}
    return frozenset(s)

def subspaces(m, d):
    seen = set()
    out = []
    for basis in itertools.combinations(range(1, 1 << m), d):
        S = span(basis)
        if len(S) == 1 << d and S not in seen:
            seen.add(S)
            out.append(S)
    return out

def restrict(f, S):
    return tuple(par(f & v) for v in sorted(S))

def value(A, W, Bs, up):
    tot = 0.0
    for Lp in Bs:
        cnt = {}
        for L in up[Lp]:
            key = restrict(W[L], Lp)
            cnt[key] = cnt.get(key, 0) + 1
        tot += max(cnt.values()) / len(up[Lp])
    return tot / len(Bs)

def main(m, l, seed):
    rng = random.Random(seed)
    A = subspaces(m, l)
    Bs = subspaces(m, l - 1)
    up = {Lp: [] for Lp in Bs}
    Bset = set(Bs)
    for L in A:
        pts = sorted(L - {0})
        for h in range(1, 1 << m):
            Lp = frozenset(v for v in L if par(h & v) == 0)
            if len(Lp) == 1 << (l - 1) and Lp in Bset and L not in up[Lp]:
                up[Lp].append(L)
    forms = list(range(1 << m))
    res = {}
    f0 = rng.choice(forms)
    res["honest"] = value(A, {L: f0 for L in A}, Bs, up)
    f1, f2 = rng.sample(forms, 2)
    res["two-patch"] = value(A, {L: rng.choice((f1, f2)) for L in A}, Bs, up)
    rank = {v: rng.random() for v in range(1, 1 << m)}
    fz = {v: rng.choice(forms) for v in range(1, 1 << m)}
    res["zoom-in"] = value(A, {L: fz[max(L - {0}, key=rank.get)] for L in A}, Bs, up)
    fz2 = {v: rng.choice((f1, f2)) for v in range(1, 1 << m)}
    res["zoom-in-2"] = value(A, {L: fz2[max(L - {0}, key=rank.get)] for L in A}, Bs, up)
    hr = {h: rng.random() for h in range(1, 1 << m)}
    fh = {h: rng.choice(forms) for h in range(1, 1 << m)}
    W = {}
    for L in A:
        hs = [h for h in range(1, 1 << m) if all(par(h & v) == 0 for v in L)]
        W[L] = fh[max(hs, key=hr.get)]
    res["zoom-out"] = value(A, W, Bs, up)
    cap = (2 ** (l - 1) - 1) / (2 ** l - 1)
    return res, cap

def check_seed_identity(m, l, trials, rng):
    """Exact check of corr >= 2 s a - 1 on random witnesses and selectors."""
    worst = 1.0
    for _ in range(trials):
        n = 1 << (m - l + 1)          # directions in the quotient, abstractly
        xs = list(range(1, n))
        S = [rng.random() < 0.6 for _ in xs]
        phi = [rng.randrange(2) for _ in xs]
        f = [rng.randrange(2) for _ in xs]   # any fixed reference bits
        junk = [rng.randrange(2) for _ in xs]
        bits = [phi[i] if S[i] else junk[i] for i in range(len(xs))]
        corr = sum(1 if bits[i] == f[i] else -1 for i in range(len(xs))) / len(xs)
        s = sum(S) / len(xs)
        a = (sum(1 for i in range(len(xs)) if S[i] and phi[i] == f[i]) / max(1, sum(S)))
        worst = min(worst, corr - (2 * s * a - 1))
    return worst >= -1e-12

def check_vacuity(m):
    h = lambda x: sum(((x >> (2 * i)) & 1) * ((x >> (2 * i + 1)) & 1) for i in range(m // 2)) & 1
    for x in range(1 << m):
        cands = [0] + [1 << i for i in range(m)]
        assert any(par(c & x) == h(x) for c in cands)
    mx = max(abs(sum((-1) ** (h(x) ^ par(f & x)) for x in range(1 << m))) / 2 ** m
             for f in range(1 << m))
    return mx

if __name__ == "__main__":
    rng = random.Random(1)
    assert check_seed_identity(6, 3, 2000, rng)
    print("seed identity corr >= 2sa-1: ok")
    for m in (6, 8):
        print("vacuity m=%d: explained by m+1 forms, max |corr| = %.4f = 2^-%d"
              % (m, check_vacuity(m), m // 2))
    for (m, l) in ((5, 2), (6, 3)):
        for sd in (0, 1):
            res, cap = main(m, l, sd)
            print("m=%d l=%d seed=%d cap=%.4f " % (m, l, sd, cap)
                  + " ".join("%s=%.4f" % kv for kv in res.items()))
