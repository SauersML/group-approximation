"""Rigorous lower bound for delta_2 on every two-dimensional profile other than
the minimiser's, by a grid plus a Lipschitz bound.

D(t) = max_r ||r(A, B_t) - 1||, B_t = R(t) B0 R(t)^T.  dB_t/dt = [R'R^T, B_t] has
norm <= 2.  The longest relator r_2 has 16 letters B^{+-1}; the relators contain
A and J only as fixed letters.  Hence |D(t) - D(s)| <= 32 |t - s|, and on a grid
of spacing h the true minimum is >= (grid minimum) - 16 h.

For the minimiser's profile p = (1,3), q = (1,2) the proof node uses the exact
SU(2) trace formulas instead; this script also evaluates them against the matrix
computation as a consistency check.
Output: out_dim2_lipschitz.json
"""
import itertools, json, math
import numpy as np
from census import relators

I4 = [np.exp(1j * np.pi * j / 2) for j in range(4)]
W3 = [np.exp(2j * np.pi * j / 3) for j in range(3)]


def D(p, q, t):
    c, s = math.cos(t), math.sin(t)
    Y = np.array([[c, -s], [s, c]], dtype=complex)
    A = np.diag([I4[p[0]], I4[p[1]]])
    B = Y @ np.diag([W3[q[0]], W3[q[1]]]) @ Y.T
    return {k: float(np.linalg.norm(R - np.eye(2), 2)) for k, R in relators(A, B).items()}

N = 16001
h = (math.pi / 2) / (N - 1)
L = 32.0
out = {"grid_points": N, "spacing": h, "lipschitz": L, "profiles": []}
ts = np.linspace(0, math.pi / 2, N)
for p in itertools.permutations(range(4), 2):
    for q in itertools.permutations(range(3), 2):
        if p[0] > p[1] or q[0] > q[1]:
            continue
        vals = np.array([max(D(p, q, t).values()) for t in ts])
        gmin = float(vals.min())
        out["profiles"].append({"p": p, "q": q, "grid_min": gmin, "certified_lower": gmin - L * h / 2,
                                "argmin_t": float(ts[int(vals.argmin())])})
# trace-formula check on the minimiser's profile
err = 0.0
for t in ts[::50]:
    d = D((1, 3), (1, 2), t)
    x = -math.sqrt(3) * math.cos(2 * t)
    phi = math.acos(max(-1.0, min(1.0, x / 2)))
    err = max(err, abs(d["r2"] - math.sqrt(max(0.0, 3 - x * x))), abs(d["rP"] - 2 * abs(math.sin(2.5 * phi))),
              abs(d["r1"]))
out["trace_formula_max_error"] = err
out["profiles"].sort(key=lambda r: r["grid_min"])
json.dump(out, open("out_dim2_lipschitz.json", "w"), indent=1)
for r in out["profiles"]:
    print(r)
print("trace formula max error", err)
