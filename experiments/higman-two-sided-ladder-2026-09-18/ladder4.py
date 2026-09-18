#!/usr/bin/env python3
"""Order-2 tower invariant for the k = 4 chain (b, d, b, d) in Higman's group.

S2(u) = sum over alpha-letters lam of u of  eps_lam * s^(h(lam)) * T^(Gamma(lam)),
  h(lam)      = gamma-height of lam,
  Gamma(lam)  = the function kappa -> net gamma-exponent of the gamma-letters l before lam with
                kappa(l) = kappa, where kappa(l)(h) = net alpha-exponent before l at gamma-height h.
For u1 = iota_b(w0), w0 in F^(4), S2(u1) != 0 implies (for large shifts) that the k = 4 chain
produces a word with exponent sums (X, 0), X != 0.
"""
import sys
from collections import Counter
sys.path.insert(0, __file__.rsplit('/', 1)[0])
from ladder import A, a_, C, c_, red, inv, mul, comm, cj, exps, iota_b, in_P_ge0, S_numeric


def S2_numeric(u):
    kappa = Counter()
    Gam = Counter()
    g = 0
    S2 = Counter()
    for x in u:
        if abs(x) == 2:
            e = 1 if x == C else -1
            key = frozenset(kappa.items())
            Gam[key] += e
            if Gam[key] == 0:
                del Gam[key]
            g += e
        else:
            e = 1 if x == A else -1
            S2[(g, frozenset(Gam.items()))] += e
            kappa[g] += e
            if kappa[g] == 0:
                del kappa[g]
    return Counter({k: v for k, v in S2.items() if v})


def Sb_numeric(u):
    """Mirror of S: sum over alpha-letters of eps * t^K, K(j) = net gamma-exponent before, at alpha-height j."""
    K = Counter()
    h = 0
    S = Counter()
    for x in u:
        if abs(x) == 2:
            e = 1 if x == C else -1
            K[h] += e
            if K[h] == 0:
                del K[h]
        else:
            e = 1 if x == A else -1
            S[frozenset(K.items())] += e
            h += e
    return Counter({k: v for k, v in S.items() if v})


def iota_d(v, P):
    out, h = [], 0
    for x in v:
        if abs(x) == 2:
            h += 1 if x == C else -1
            out.append(x)
        else:
            if h < 0:
                raise ValueError("alpha-letter at negative gamma-height")
            out.extend([x] * (2 ** (P ** h)))
    return red(out)


def brute_force_identity():
    """Check S^b(iota_d(v)) = sum_lam eps N_h(lam) t^(pi_* Gamma(lam)), pi(kappa) = sum_h N_h kappa_h."""
    import random
    rnd = random.Random(7)
    P = 2
    N = lambda h: 2 ** (P ** h)

    def rword():
        r = []
        for _ in range(rnd.randint(1, 4)):
            i = rnd.randint(0, 2)
            e = rnd.choice((1, -1))
            r = mul(r, [C] * i, [A] if e > 0 else [a_], [c_] * i)
        return r
    checked = 0
    for trial in range(200):
        v = comm(comm(rword(), rword()), comm(rword(), rword())) if trial % 2 else comm(rword(), rword())
        if not v:
            continue
        u2 = iota_d(v, P)
        direct = Sb_numeric(u2)
        S2 = S2_numeric(v)
        pred = Counter()
        for (h, G), eps in S2.items():
            push = Counter()
            for kap, val in G:
                push[sum(cnt * N(hh) for hh, cnt in kap)] += val
            key = frozenset((j, w) for j, w in push.items() if w)
            pred[key] += eps * N(h)
        pred = Counter({k: w for k, w in pred.items() if w})
        assert pred == direct, (v,)
        checked += 1
    return checked


def S2_symbolic(w0):
    """Formal S2(iota_b(w0)) for w0 with gamma-letters at alpha-heights 0, 1 only; N_0 = 2, N_1 = M formal.

    gamma-heights are 2p + qM, stored as (p, q); Gamma-values are 2 c0 + M c1, stored as (c0, c1)."""
    kappa = Counter()     # (p, q) -> net alpha exponent
    Gam = {}              # kappa-key -> (c0, c1)
    p = q = 0
    ah = 0
    S2 = Counter()
    heights, c0s = [(0, 0)], [0]
    for x in w0:
        if abs(x) == 2:
            e = 1 if x == C else -1
            key = frozenset(kappa.items())
            c0, c1 = Gam.get(key, (0, 0))
            Gam[key] = (c0 + e, c1) if ah == 0 else (c0, c1 + e)
            if Gam[key] == (0, 0):
                del Gam[key]
            if ah == 0:
                p += e
            else:
                q += e
            heights.append((p, q))
        else:
            e = 1 if x == A else -1
            S2[((p, q), frozenset(Gam.items()))] += e
            c0s.extend(v[0] for v in Gam.values())
            kappa[(p, q)] += e
            if kappa[(p, q)] == 0:
                del kappa[(p, q)]
            ah += e
    S2 = Counter({k: v for k, v in S2.items() if v})
    prange = max(h[0] for h in heights) - min(h[0] for h in heights)
    c0range = max(c0s) - min(c0s)
    return S2, prange, c0range


def main():
    print("brute-force check of S^b(iota_d(v)) = pushforward of S2(v):", brute_force_identity(),
          "random words agree")
    x = mul(cj(1), cj(0, -1))
    y = mul(cj(0, -1), cj(1))
    x2 = mul(cj(0), cj(1), cj(0, -2))
    y2 = mul(cj(1, -1), cj(0), cj(1, -1), cj(0))
    f2a, f2b, f2c = comm(x, y), comm(x2, y2), comm(y, x2)
    f3a, f3b, f3c = comm(f2a, f2c), comm(f2a, f2b), comm(f2b, f2c)
    # calibration: at k = 3 the order-2 invariant of u1 must vanish? (no claim) -- we print S and S2
    for name, w0 in [("[f3a,f3b]", comm(f3a, f3b)), ("[f3a,f3c]", comm(f3a, f3c))]:
        assert in_P_ge0(w0) and exps(w0) == (0, 0)
        for P in (2, 4, 8):
            u1 = iota_b(w0, P)
            S2 = S2_numeric(u1)
            S1 = S_numeric(u1)
            print(f"k=4 w0={name} |w0|={len(w0)} P={P}: |u1|={len(u1)}, S(u1) nonzero: {bool(S1)}, "
                  f"S2(u1) nonzero: {bool(S2)} ({len(S2)} terms, l1 = {sum(abs(v) for v in S2.values())})")
            sys.stdout.flush()
        S2f, prange, c0range = S2_symbolic(w0)
        M0 = max(2 * prange, 2 * c0range)
        print(f"  symbolic (N_1 = M formal): {len(S2f)} nonzero formal terms, p-range {prange}, "
              f"c0-range {c0range}; formal keys stay distinct, so S2 != 0, for every M > {M0}")


if __name__ == "__main__":
    main()
