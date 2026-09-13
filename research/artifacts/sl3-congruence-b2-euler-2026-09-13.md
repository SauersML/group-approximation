# Euler characteristics of congruence quotients over the Soulé sector (lane ex-hs-instability-kazhdan, 2026-09-13)

This is the script and raw output behind `sl3-polynomial-congruence-subgroups-have-large-b2`.
- **Run.** `/usr/bin/python3.11` on MSI, under
  `/scratch.global/sauer354/ex/ex-hs-instability-kazhdan/`; runtime a few seconds.
- **What it computes.** `χ(Y_R) = Σ_(σ ⊂ Q_R) (-1)^(dim σ) |SL_3(A)|/|π(Γ_σ)|` for `R = 0..12`.
- **What the image orders depend on.** Only the degree `D` of `f`. The order `|SL_3(A)|` depends
  on the factorization type, given as a list of (degree of prime factor, exponent).

## Raw output

```text
2 t [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1]
2 t^2 [256, 256, 928, 928, 928, 928, 928, 928, 928, 928, 928, 928, 928]
2 t(t+1) [168, 168, 609, 609, 609, 609, 609, 609, 609, 609, 609, 609, 609]
2 t^3 [65536, 65536, 323584, 409600, 431104, 431104, 431104, 431104, 431104, 431104, 431104, 431104, 431104]
2 irred deg2 [360, 360, 1305, 1305, 1305, 1305, 1305, 1305, 1305, 1305, 1305, 1305, 1305]
3 t [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1]
3 t^2 [6561, 82377, 132921, 132921, 132921, 132921, 132921, 132921, 132921, 132921, 132921, 132921, 132921]
3 t(t+1) [5616, 70512, 113776, 113776, 113776, 113776, 113776, 113776, 113776, 113776, 113776, 113776, 113776]
3 t^3 [43046721, 540475497, 1037904273, 1111597425, 1123879617, 1123879617, 1123879617, 1123879617, 1123879617, 1123879617, 1123879617, 1123879617, 1123879617]
3 irred deg2 [7560, 94920, 153160, 153160, 153160, 153160, 153160, 153160, 153160, 153160, 153160, 153160, 153160]
```

**Checks.**
- **Calibration.** Level `t` gives `χ = 1` at every `R`: the quotient is the cone over the
  spherical building.
- **Stabilization.** Values stabilize at `R = 2D-2`, namely 2 for `D = 2` and 4 for `D = 3`. This is
  the collapse bound proved in the route.
- **By hand.** `(q,f,R) = (2,t^2,1)` gives 256.

## Script (`chi_congruence.py`)

```python
from fractions import Fraction
import sys

def gl_order(n, Q):
    o = 1
    for i in range(n):
        o *= (Q**n - Q**i)
    return o

def sl3_A_order(q, factors):
    gl = 1
    units = 1
    for (dP, e) in factors:
        Q = q**dP
        gl *= gl_order(3, Q) * Q**(9*(e-1))
        units *= (Q-1) * Q**(e-1)
    assert gl % units == 0
    return gl // units

def image_order(q, degf, verts):
    a = [(v[0], v[1], 0) for v in verts]
    d = [[min(x[i]-x[j] for x in a) for j in range(3)] for i in range(3)]
    blocks = []
    seen = set()
    for i in range(3):
        if i in seen:
            continue
        blk = [j for j in range(3) if d[i][j] >= 0 and d[j][i] >= 0]
        for j in blk:
            seen.add(j)
        blocks.append(len(blk))
    levi = 1
    for n in blocks:
        levi *= gl_order(n, q)
    levi //= (q-1)
    up = 1
    for i in range(3):
        for j in range(3):
            if i != j and d[i][j] >= 0 and d[j][i] < 0:
                up *= q**min(d[i][j]+1, degf)
    return levi * up

def cells(R):
    V = [(a, b) for a in range(R+1) for b in range(a+1)]
    Vs = set(V)
    E, T = [], []
    for v in V:
        for dv in [(1, 0), (0, 1), (1, 1)]:
            w = (v[0]+dv[0], v[1]+dv[1])
            if w in Vs:
                E.append((v, w))
        for tri in [((1, 0), (1, 1)), ((0, 1), (1, 1))]:
            w1 = (v[0]+tri[0][0], v[1]+tri[0][1]); w2 = (v[0]+tri[1][0], v[1]+tri[1][1])
            if w1 in Vs and w2 in Vs:
                T.append((v, w1, w2))
    return V, E, T

def chi(q, factors, R):
    degf = sum(dP*e for dP, e in factors)
    G = sl3_A_order(q, factors)
    V, E, T = cells(R)
    tot = 0
    for sig, sign in [(V, 1), (E, -1), (T, 1)]:
        for c in sig:
            verts = [c] if sign == 1 and len(c) == 2 and isinstance(c[0], int) else list(c)
            o = image_order(q, degf, verts)
            assert G % o == 0, (c, G, o)
            tot += sign * (G // o)
    return tot

if __name__ == "__main__":
    for q in [2, 3]:
        for name, factors in [("t", [(1, 1)]), ("t^2", [(1, 2)]), ("t(t+1)", [(1, 1), (1, 1)]),
                              ("t^3", [(1, 3)]), ("irred deg2", [(2, 1)])]:
            vals = [chi(q, factors, R) for R in range(0, 13)]
            print(q, name, vals)
    sys.stdout.flush()
```
