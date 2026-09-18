#!/usr/bin/env python3
"""Order-r tower invariants S_r for the k-step two-sided chain in Higman's group (k = r + 2).

Word u1 = iota_b(w0) is processed in block form: a gamma-letter of w0 at alpha-height j becomes one
block of weight eps * N_j (N_0 = 2, N_1 = 2^P); an alpha-letter has weight eps.

Types (d-flavoured; tau_0 of an alpha-letter is its gamma-height):
  tau_0(lam) = gamma-height of lam,        tau_{-1}(l) = trivial,
  tau_r(x)   = ( tau_{r-2}(x),  PS_{r-1}(x) ),
  PS_{r-1}(x) = sum over earlier letters y of the other kind of weight_y [tau_{r-1}(y)],
  r even <-> alpha-letters, r odd <-> gamma-letters.
  S_r(u) = sum over letters x of kind r of weight_x [tau_r(x)].
S_0 = E^d, S_1 = S, S_2 = S2 of ladder.py / ladder4.py.

Implementation: types are hashed; formal sums are hashed linearly (mod 2^61 - 1).  The hash of a
type is a function of the type, so a nonzero hash of S_r certifies S_r != 0 (a collision can only
hide a nonzero value, never create one).

Modes:
  numeric  : exact integer heights and weights for a given P = 2^m;
  symbolic : N_1 = M formal; heights stored as (p, q) meaning 2p + qM, gamma-weights as (c0, c1)
             meaning 2c0 + M c1.  Formal S_r != 0 implies S_r != 0 for every M > bound, where
             bound = max(2 * prange, 4 * n0) and n0 = number of gamma-letters of w0 at alpha-height 0
             (|c0| <= n0 for every coefficient, and distinct coefficients have |c0 - c0'| <= 2 n0).
"""
import sys
sys.path.insert(0, __file__.rsplit('/', 1)[0])
from ladder import A, a_, C, c_, red, mul, comm, cj, exps, in_P_ge0

MOD = (1 << 61) - 1
MASK = (1 << 64) - 1


def mix(x):
    x = (x + 0x9E3779B97F4A7C15) & MASK
    x = ((x ^ (x >> 30)) * 0xBF58476D1CE4E5B9) & MASK
    x = ((x ^ (x >> 27)) * 0x94D049BB133111EB) & MASK
    return (x ^ (x >> 31)) % MOD


def hpair(a, b):
    return mix(mix(a) * 1000003 + b)


def height_hash(h):
    # h is an int (numeric) or a pair (p, q) (symbolic)
    if isinstance(h, tuple):
        return mix((h[0] % MOD) * 7919 + mix(h[1] % MOD))
    return mix(h % MOD)


def tower(w0, R, P=None):
    """Return list [S_0 hash, ..., S_R hash] of u1 = iota_b(w0); P numeric or None (symbolic)."""
    TRIV = mix(123456789)
    nlev = R + 1
    # prefix sums: numeric -> one hash per level; symbolic -> (hash_c0, hash_c1) for gamma levels
    PS = [[0, 0] for _ in range(nlev)]
    ah = 0
    if P is None:
        g = (0, 0)
    else:
        g = 0
        N1 = 2 ** P
    for x in w0:
        if abs(x) == 2:
            e = 1 if x == C else -1
            assert ah >= 0
            if P is None:
                assert ah in (0, 1)
                wt = (e, 0) if ah == 0 else (0, e)
            else:
                wt = (e * (2 ** (P ** ah)), 0)
            # types of this gamma-letter at odd levels
            prev = TRIV
            for r in range(1, nlev, 2):
                ps = PS[r - 1][0]
                t = hpair(prev, ps)
                PS[r][0] = (PS[r][0] + wt[0] * mix(t)) % MOD
                PS[r][1] = (PS[r][1] + wt[1] * mix(t)) % MOD
                prev = t
            if P is None:
                g = (g[0] + wt[0], g[1] + wt[1])
            else:
                g += wt[0]
        else:
            e = 1 if x == A else -1
            prev = height_hash(g)
            PS[0][0] = (PS[0][0] + e * mix(prev)) % MOD
            for r in range(2, nlev, 2):
                ps = hpair(PS[r - 1][0], PS[r - 1][1])
                t = hpair(prev, ps)
                PS[r][0] = (PS[r][0] + e * mix(t)) % MOD
                prev = t
            ah += e
    return [tuple(p) for p in PS]


def tower_exact(w0, R, P):
    """Unhashed tower (numeric P): exact nested types and formal sums, same recursion as tower().

    Returns (list of exact S_r as dicts, list of hashes recomputed from the exact data)."""
    nlev = R + 1
    PS = [dict() for _ in range(nlev)]
    ah = g = 0

    def add(d, t, c):
        d[t] = d.get(t, 0) + c
        if d[t] == 0:
            del d[t]

    def freeze(d):
        return frozenset(d.items())

    for x in w0:
        if abs(x) == 2:
            e = 1 if x == C else -1
            wt = e * (2 ** (P ** ah))
            prev = ('T',)
            for r in range(1, nlev, 2):
                t = (prev, freeze(PS[r - 1]))
                add(PS[r], t, wt)
                prev = t
            g += wt
        else:
            e = 1 if x == A else -1
            prev = ('h', g)
            add(PS[0], prev, e)
            for r in range(2, nlev, 2):
                t = (prev, freeze(PS[r - 1]))
                add(PS[r], t, e)
                prev = t
            ah += e

    memo = {}

    def H(t, alpha_level):
        key = (t, alpha_level)
        if key in memo:
            return memo[key]
        if t == ('T',):
            v = mix(123456789)
        elif t[0] == 'h':
            v = height_hash(t[1])
        else:
            prev, s = t
            hs = Hsum(s, not alpha_level)
            v = hpair(H(prev, alpha_level), hpair(hs, 0) if alpha_level else hs)
        memo[key] = v
        return v

    def Hsum(s, alpha_level):
        return sum(c * mix(H(t, alpha_level)) for t, c in s) % MOD

    hashes = [Hsum(freeze(PS[r]), r % 2 == 0) for r in range(nlev)]
    return PS, hashes


def crosscheck():
    """Compare the hashed tower with the exact one on the chain words and on random words of P_{>=0}."""
    import random
    rnd = random.Random(11)
    n = 0
    for k in (2, 3, 4):
        for w0 in build(k)[:2]:
            for P in (2, 4):
                S, hs = tower_exact(w0, k - 2, P)
                th = tower(w0, k - 2, P)
                assert [h for h in hs] == [t[0] for t in th], (k, P)
                assert [bool(s) for s in S] == [t != (0, 0) for t in th]
                n += 1

    def rword():
        r = []
        for _ in range(rnd.randint(1, 5)):
            r = mul(r, cj(rnd.randint(0, 2), rnd.choice((1, -1))))
        return r
    zeros = [0] * 4
    for trial in range(300):
        u = comm(rword(), rword())
        if trial % 3 == 1:
            u = comm(u, comm(rword(), rword()))
        if trial % 3 == 2:
            u = mul(u, rword())
        if not u:
            continue
        S, hs = tower_exact(u, 3, 2)
        th = tower(u, 3, 2)
        assert hs == [t[0] for t in th]
        assert [bool(s) for s in S] == [t != (0, 0) for t in th]
        for r in range(4):
            zeros[r] += not S[r]
        n += 1
    return n, zeros


def flavoured(u, R, flavour):
    """Exact tower of a plain word u.  flavour 'd': kind-0 letters are alpha, typed by gamma-height;
    flavour 'b': kind-0 letters are gamma, typed by alpha-height.  Returns [S_0, ..., S_R] as dicts."""
    k0 = A if flavour == 'd' else C
    PS = [dict() for _ in range(R + 1)]
    ht = 0

    def add(d, t, c):
        d[t] = d.get(t, 0) + c
        if d[t] == 0:
            del d[t]
    for x in u:
        e = 1 if x > 0 else -1
        if abs(x) == abs(k0):
            prev = ('h', ht)
            add(PS[0], prev, e)
            levels = range(2, R + 1, 2)
        else:
            prev = ('T',)
            levels = range(1, R + 1, 2)
            ht += e
        for r in levels:
            t = (prev, frozenset(PS[r - 1].items()))
            add(PS[r], t, e)
            prev = t
    return PS


def sigma_push(S, N):
    """sigma_*: d-flavoured formal sum at level r+1 -> b-flavoured formal sum at level r (see proof)."""
    memo = {}

    def root(t):
        while t[0] not in ('h', 'T'):
            t = t[0]
        return t

    def wt(t):
        rt = root(t)
        return N(rt[1]) if rt[0] == 'h' else 1

    def sig(t):
        if t in memo:
            return memo[t]
        if t[0] == 'h':
            v = ('T',)
        else:
            prev, s = t
            if prev == ('T',):          # d-level 1: kappa -> alpha-height in iota_d(v)
                v = ('h', sum(c * wt(tt) for tt, c in s))
            else:
                v = (sig(prev), frozenset(push(s).items()))
        memo[t] = v
        return v

    def push(s):
        out = {}
        for t, c in (s.items() if isinstance(s, dict) else s):
            key = sig(t)
            out[key] = out.get(key, 0) + c * wt(t)
            if out[key] == 0:
                del out[key]
        return out
    return push(S)


def one_step_check(trials=150, R=4):
    """Check S^b_r(iota_d(v)) = sigma_*(S^d_{r+1}(v)) for r = 0..R-1 on random v with alpha-letters at
    gamma-height >= 0 (P = 2)."""
    import random
    from ladder4 import iota_d
    rnd = random.Random(5)
    P = 2
    N = lambda h: 2 ** (P ** h)

    def dj(i, e=1):              # gamma^i alpha^e gamma^-i
        return mul([C] * i, [A] * e if e > 0 else [a_] * (-e), [c_] * i)

    def rword():
        r = []
        for _ in range(rnd.randint(1, 4)):
            r = mul(r, dj(rnd.randint(0, 2), rnd.choice((1, -1))))
        return r
    checked = 0
    for trial in range(trials):
        v = comm(rword(), rword())
        if trial % 3 == 1:
            v = comm(v, comm(rword(), rword()))
        if trial % 3 == 2:
            v = mul(v, rword(), [C] * rnd.randint(0, 2))
        if not v:
            continue
        Sd = flavoured(v, R, 'd')
        Sb = flavoured(iota_d(v, P), R - 1, 'b')
        for r in range(R):
            assert Sb[r] == sigma_push(Sd[r + 1], N), (v, r)
        checked += 1
    return checked


def conjugation_check(trials=200, R=4):
    """Check: if S^d_r(u) != 0 then S^d_r(gamma^n u gamma^-n) = 0 for at most one n (n = 0..6); and
    S^d_r(u) = 0 with trivial end type gives S^d_r(gamma^n u gamma^-n) = 0 for all n."""
    import random
    rnd = random.Random(3)

    def rword():
        r = []
        for _ in range(rnd.randint(1, 5)):
            j = rnd.randint(-2, 2)
            r = mul(r, ([C] * j if j > 0 else [c_] * -j) if rnd.random() < 0.5 else [A if rnd.random() < .5 else a_])
        return r
    worst = 0
    checked = 0
    for trial in range(trials):
        u = comm(rword(), rword())
        if trial % 2:
            u = comm(u, comm(rword(), rword()))
        if not u:
            continue
        S = flavoured(u, R, 'd')
        for r in range(R + 1):
            if S[r]:
                bad = sum(1 for n in range(7) if not flavoured(mul([C] * n, u, [c_] * n), R, 'd')[r])
                worst = max(worst, bad)
                assert bad <= 1
        checked += 1
    return checked, worst


def build(k):
    """An element of F^(k) in <c_0, c_1>: iterated commutators of the words of ladder.py."""
    x = mul(cj(1), cj(0, -1))
    y = mul(cj(0, -1), cj(1))
    x2 = mul(cj(0), cj(1), cj(0, -2))
    y2 = mul(cj(1, -1), cj(0), cj(1, -1), cj(0))
    layer = [x, y, x2, y2]          # in F'
    for level in range(2, k + 1):
        n = len(layer)
        layer = [comm(layer[0], layer[1]), comm(layer[1], layer[2 % n]),
                 comm(layer[2 % n], layer[3 % n]), comm(layer[0], layer[3 % n])]
        layer = [w for w in layer if w] or layer
    return layer


def main():
    kmax = int(sys.argv[1]) if len(sys.argv) > 1 else 5
    n, zeros = crosscheck()
    print(f"cross-check: hashed tower = exact tower (hash values and zero patterns) on {n} words; "
          f"exact zeros among random words at levels 0..3: {zeros}")
    print(f"one-step lemma S^b_r(iota_d(v)) = sigma_*(S^d_(r+1)(v)), r = 0..3, P = 2: "
          f"{one_step_check()} random words agree")
    print("conjugation lemma (nonzero S^d_r(u) survives gamma^n-conjugation for all but <= 1 n), "
          "r = 0..4, n = 0..6: (words checked, worst number of bad n) =", conjugation_check())
    sys.stdout.flush()
    for k in range(2, kmax + 1):
        cands = build(k)
        for idx, w0 in enumerate(cands[:2]):
            assert in_P_ge0(w0) and exps(w0) == (0, 0)
            n0, h = 0, 0
            for x in w0:
                if abs(x) == 1:
                    h += 1 if x == A else -1
                elif h == 0:
                    n0 += 1
            R = k - 2
            res = []
            for m in (1, 2, 3, 4):
                S = tower(w0, R, P=2 ** m)
                res.append(f"m={m}: " + "".join("1" if s != (0, 0) else "0" for s in S))
            Sf = tower(w0, R, P=None)
            # p-range of heights
            p = ah = 0
            ps = [0]
            for x in w0:
                if abs(x) == 1:
                    ah += 1 if x == A else -1
                elif ah == 0:
                    p += 1 if x == C else -1
                    ps.append(p)
            bound = max(2 * (max(ps) - min(ps)), 4 * n0)
            mmin = next(m for m in range(1, 20) if 2 ** (2 ** m) > bound)
            print(f"k={k} w0#{idx} |w0|={len(w0)}  S_0..S_{R} nonzero pattern: " + "  ".join(res) +
                  f"  symbolic: " + "".join("1" if s != (0, 0) else "0" for s in Sf) +
                  f" (valid for M > {bound}, i.e. m >= {mmin})")
            sys.stdout.flush()


if __name__ == "__main__":
    main()
