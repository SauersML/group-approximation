"""Exact value of gamma_2 for the triangle cover Delta(4,3,5) -> T.

gamma_n = min over nontrivial genuine unitary representations rho of
Delta(4,3,5) = <a, b | a^4, b^3, (ba)^5> in U(n) of
    max( ||r_1(rho) - 1||, ||r_2(rho) - 1|| ),
with the Lochak--Schneps relators (same words as
experiments/thompson-t-opnorm-defect-gap-2026-09-17/verify_ls.py):
    r_1 = [bab, a^2 bab a^2],  r_2 = [bab, a^2 b^2 a^2 bab a^2 b a^2].

n = 2.  Delta(4,3,5) is perfect, so det rho = 1 and rho lands in SU(2).
Reducible 2-dim reps are sums of characters, hence trivial.  An irreducible
pair in SU(2) is determined up to conjugacy by (tr A, tr B, tr BA):
  A^4 = 1, A != +-1 (A = -1 forces B^2 = -1, impossible) -> tr A = 0;
  B^3 = 1, B != 1 (B = w*1 has det != 1)                   -> tr B = -1;
  (BA)^5 = 1, BA != 1 (A = B^-1 has order 3)              -> tr BA = 2cos(2 pi k/5), k = 1, 2.
So there are exactly two irreducible reps (Galois conjugate), and
gamma_2 is the smaller of their two relator maxima.  For g in SU(2),
||g - 1||^2 = 2 - tr g.
"""
import json
import mpmath as mp

mp.mp.dps = 50


def mat(a, b, c, d):
    return mp.matrix([[a, b], [c, d]])


def inv(M):
    return M.H  # unitary


def word(gens, w):
    M = mp.eye(2)
    for ch in w:
        if ch.islower():
            M = M * gens[ch]
        else:
            M = M * inv(gens[ch.lower()])
    return M


def comm(x, y):
    iw = lambda w: "".join(ch.swapcase() for ch in reversed(w))
    return x + y + iw(x) + iw(y)


X = "bab"
R1 = comm(X, "aa" + X + "aa")
R2 = comm(X, "aabbaa" + X + "aabaa")


def opnorm_minus_one(M):
    D = M - mp.eye(2)
    s = mp.svd_c(D, compute_uv=False)
    return max(abs(v) for v in s)


def rep(k):
    t = 2 * mp.cos(2 * mp.pi * k / 5)
    A = mat(1j, 0, 0, -1j)
    p = mp.mpc(-0.5, -t / 2)          # tr B = 2 Re p = -1, tr BA = -2 Im p = t
    q = mp.sqrt(1 - abs(p) ** 2)
    B = mat(p, q, -mp.conj(q), mp.conj(p))
    return A, B, t


out = {}
for k in (1, 2):
    A, B, t = rep(k)
    g = {"a": A, "b": B}
    checks = {
        "||A^4-1||": opnorm_minus_one(word(g, "aaaa")),
        "||B^3-1||": opnorm_minus_one(word(g, "bbb")),
        "||(BA)^5-1||": opnorm_minus_one(word(g, "ba" * 5)),
    }
    r1 = opnorm_minus_one(word(g, R1))
    r2 = opnorm_minus_one(word(g, R2))
    tr1 = word(g, R1)[0, 0] + word(g, R1)[1, 1]
    tr2 = word(g, R2)[0, 0] + word(g, R2)[1, 1]
    out["k=%d" % k] = {
        "tr_BA": mp.nstr(t, 20),
        "exactness": {kk: mp.nstr(v, 5) for kk, v in checks.items()},
        "||r_1-1||": mp.nstr(r1, 20),
        "||r_2-1||": mp.nstr(r2, 20),
        "sqrt(2-tr r_1)": mp.nstr(mp.sqrt(2 - mp.re(tr1)), 20),
        "sqrt(2-tr r_2)": mp.nstr(mp.sqrt(2 - mp.re(tr2)), 20),
        "max": mp.nstr(max(r1, r2), 20),
    }

gamma2 = min(mp.mpf(out[k]["max"]) for k in out)
out["gamma_2"] = mp.nstr(gamma2, 20)
out["delta_1 = 2 sin(pi/12)"] = mp.nstr(2 * mp.sin(mp.pi / 12), 20)
out["delta_2 (w17 census node)"] = "0.3491491"
print(json.dumps(out, indent=2))
with open(__file__.replace("gamma2.py", "out_gamma2.json"), "w") as f:
    json.dump(out, f, indent=2)
