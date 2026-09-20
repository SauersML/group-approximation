"""Dimension two: delta_2 as a one-parameter minimisation, certified.

An irreducible pair in U(2) has A = diag(i^p1, i^p2), p1 != p2, and
B = Y diag(w^q1, w^q2) Y*, q1 != q2.  Conjugating by diagonal unitaries
(which commute with A) and absorbing right diagonal factors into B's
eigenbasis, Y can be taken to be the real rotation by t in [0, pi/2].
So delta_2 = min over the finitely many profiles and t of D(t).

We grid t finely, refine with golden section, and then CERTIFY the best
pair with mpmath at 50 digits (A, B built exactly from the rotation, so
A^4 = B^3 = 1 up to 1e-50, and D evaluated as an exact 2x2 singular value).
Output: out_dim2_exact.json
"""
import itertools, json, math
import numpy as np
import mpmath as mp

mp.mp.dps = 50


def pair(p, q, t, lib=np):
    if lib is np:
        i4 = [np.exp(1j * np.pi * j / 2) for j in range(4)]
        w3 = [np.exp(2j * np.pi * j / 3) for j in range(3)]
        c, s = np.cos(t), np.sin(t)
        Y = np.array([[c, -s], [s, c]], dtype=complex)
        A = np.diag([i4[p[0]], i4[p[1]]])
        B = Y @ np.diag([w3[q[0]], w3[q[1]]]) @ Y.conj().T
        return A, B
    i4 = [mp.expjpi(mp.mpf(j) / 2) for j in range(4)]
    w3 = [mp.expjpi(mp.mpf(2 * j) / 3) for j in range(3)]
    c, s = mp.cos(t), mp.sin(t)
    Y = mp.matrix([[c, -s], [s, c]])
    A = mp.diag([i4[p[0]], i4[p[1]]])
    B = Y * mp.diag([w3[q[0]], w3[q[1]]]) * Y.T
    return A, B


def rels(A, B, lib=np):
    if lib is np:
        H = lambda M: M.conj().T
        I = np.eye(2)
        mul = lambda *Ms: np.linalg.multi_dot(Ms) if len(Ms) > 2 else Ms[0] @ Ms[1]
    else:
        H = lambda M: M.H
        I = mp.eye(2)

        def mul(*Ms):
            R = Ms[0]
            for M in Ms[1:]:
                R = R * M
            return R
    X = mul(B, A, B)
    J = mul(A, A)
    Y1 = mul(J, X, J)
    W = mul(J, B, B, J)
    Y2 = mul(W, X, H(W))
    C = mul(B, A)
    r1 = mul(X, Y1, H(X), H(Y1))
    r2 = mul(X, Y2, H(X), H(Y2))
    rP = mul(C, C, C, C, C)
    return {"r1": r1 - I, "r2": r2 - I, "rP": rP - I}


def opn(M, lib=np):
    if lib is np:
        return float(np.linalg.norm(M, 2))
    # largest singular value of a 2x2 via eigenvalues of M^H M
    G = M.H * M
    a, b, c, d = G[0, 0], G[0, 1], G[1, 0], G[1, 1]
    tr, det = (a + d).real, (a * d - b * c).real
    return mp.sqrt((tr + mp.sqrt(max(tr * tr - 4 * det, 0))) / 2)


def D(p, q, t, lib=np):
    A, B = pair(p, q, t, lib)
    r = rels(A, B, lib)
    return {k: opn(v, lib) for k, v in r.items()}


def golden(f, a, b, it=200):
    g = (math.sqrt(5) - 1) / 2
    c, d = b - g * (b - a), a + g * (b - a)
    for _ in range(it):
        if f(c) < f(d):
            b = d
        else:
            a = c
        c, d = b - g * (b - a), a + g * (b - a)
    return (a + b) / 2


results = []
for p in itertools.permutations(range(4), 2):
    for q in itertools.permutations(range(3), 2):
        if p[0] > p[1] or q[0] > q[1]:
            continue  # eigenvalue order is absorbed by t -> pi/2 - t and diagonal conjugation
        f = lambda t: max(D(p, q, t).values())
        ts = np.linspace(0, np.pi / 2, 4001)
        vals = [f(t) for t in ts]
        j = int(np.argmin(vals))
        t0 = golden(f, ts[max(j - 1, 0)], ts[min(j + 1, len(ts) - 1)])
        results.append({"p": p, "q": q, "t": t0, "D": f(t0), "parts": D(p, q, t0)})
results.sort(key=lambda r: r["D"])
best = results[0]
cert = D(best["p"], best["q"], mp.mpf(best["t"]), lib=mp)
A, B = pair(best["p"], best["q"], mp.mpf(best["t"]), lib=mp)
A4 = mp.mnorm(A * A * A * A - mp.eye(2), 1)
B3 = mp.mnorm(B * B * B - mp.eye(2), 1)
out = {
    "profiles": results,
    "best": best,
    "certificate_50_digits": {k: mp.nstr(v, 20) for k, v in cert.items()},
    "exactness_A4_B3": [mp.nstr(A4, 5), mp.nstr(B3, 5)],
    "delta_1": 2 * math.sin(math.pi / 12),
}
json.dump(out, open("out_dim2_exact.json", "w"), indent=1, default=str)
for r in results:
    print(r["p"], r["q"], round(r["t"], 6), round(r["D"], 6), {k: round(v, 6) for k, v in r["parts"].items()})
print("certificate", out["certificate_50_digits"], out["exactness_A4_B3"])
