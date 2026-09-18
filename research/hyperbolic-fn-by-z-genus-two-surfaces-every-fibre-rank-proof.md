---
rg: 2
id: hyperbolic-fn-by-z-genus-two-surfaces-every-fibre-rank-proof
kind: route
title: Feed a chain of new letters into phi(a) of the phi_1 certificate; a Pisot block polynomial and Rouché make every characteristic polynomial irreducible, and the pairing is unchanged
target: hyperbolic-fn-by-z-genus-two-surfaces-every-fibre-rank
requires:
  - legal-f-folded-fatgraphs-give-surface-subgroups
  - hyperbolic-f3-by-z-with-genus-two-surface-certificates
artifacts:
  - experiments/legal-f-folded-fatgraphs-2026-09-17/pisot_chain_family.py
  - experiments/legal-f-folded-fatgraphs-2026-09-17/pisot_chain_family_k40.log
  - experiments/legal-f-folded-fatgraphs-2026-09-17/verify_surface_rankn.py
  - experiments/legal-f-folded-fatgraphs-2026-09-17/verify_surface.py
  - experiments/legal-f-folded-fatgraphs-2026-09-17/surface_phi1028.json
---

Notation as in the claim. Upper case is inverse, `n = k + 3 >= 4`, `phi = phi_k`,
`X = a^6 c^9` (so that `phi(a) = a X d_1 b`), and `D_k = d_k^-1`.

**Step 1: automorphism.** Every generator lies in the image of `phi`:

- `b = phi(d_k)`;
- `a = b^-1 phi(c) b^-2`;
- `c = phi(b) a^-1`;
- `d_{i+1} = phi(d_i)` for `1 <= i < k`;
- `d_1 = X^-1 a^-1 phi(a) b^-1`, since `a`, `b` and `c` are already in the image.

So `phi` is surjective, and hence an automorphism, since free groups of finite rank are Hopfian.
The resulting inverse `psi` is:

- `psi(b) = d_k`, `psi(a) = D_k c D_k D_k`, `psi(c) = b psi(a)^-1`;
- `psi(d_{i+1}) = d_i`;
- `psi(d_1) = psi(X)^-1 psi(a)^-1 a psi(b)^-1`.

`pisot_chain_family.py` checks `phi o psi = psi o phi = id` by free reduction for `k <= 40`. All
images are positive, so the rose map `f_k` is a train track map (TT).

**Step 2: characteristic polynomial.** Column `x` of `M` counts the letters of `phi(x)`. Order the
basis `a, b, c | d_1, ..., d_k`. Then `tI - M = [[tI - P, -Q], [-R, tI - S]]`, where:

- `P = [[7,1,1],[1,0,3],[9,1,0]]`, with `A(t) := det(tI - P) = t^3 - 7t^2 - 13t - 7`;
- `Q` has a single entry `1` at `(b, d_k)`;
- `R` has a single entry `1` at `(d_1, a)`;
- `S` is the nilpotent shift `d_i -> d_{i+1}`.

For `t != 0`, `(tI - S)^-1 = sum_j S^j / t^{j+1}`. Its `(d_k, d_1)` entry is `t^-k`. By the Schur
complement, `chi_k(t) = t^k det(tI - P - t^-k E_{ba})`. The determinant is affine in the `(b, a)`
entry, and the cofactor of that entry is `-det[[-1, -1], [-1, t]] = t + 1`. Hence

```text
chi_k(t) = t^k A(t) - (t + 1),   chi_k(0) = -1,   chi_k(1) = A(1) - 2 = -28.
```

`pisot_chain_family.py` compares this with the exact Faddeev--LeVerrier polynomial for `k <= 40`.

**Step 3: primitivity.** Draw an arrow `x -> y` when `y` occurs in `phi(x)`. There is a loop at `a`,
and the cycle `a -> d_1 -> ... -> d_k -> b -> c -> a` passes through every letter. So `M` is
irreducible and aperiodic, hence primitive. Its Perron--Frobenius root `lambda > 1` is simple.

**Step 4: `A` is Pisot.**

- `A(8) = -47 < 0 < 38 = A(9)`, so `A` has a real root `theta` in `(8, 9)`.
- `disc(A) = -5324 < 0`, so the other two roots form a complex pair.
- The product of all three roots is `7`, so the pair has modulus squared `7 / theta < 7/8`.

**Step 5: Rouché on the unit circle.** Put `t = e^{is}` and `x = cos s`. For a real polynomial,
`|sum a_j t^j|^2 = sum_j a_j^2 + 2 sum_{m >= 1} (sum_j a_j a_{j+m}) cos(ms)`. With coefficients
`(-7, -13, -7, 1)` this gives

```text
|A(t)|^2 = 268 + 350 cos s + 72 cos 2s - 14 cos 3s,    |t + 1|^2 = 2 + 2 cos s,
G(x) := |A(t)|^2 - |t + 1|^2 = -56x^3 + 144x^2 + 390x + 194.
```

Put `y = x + 1`, with `y` in `[0, 2]`. Then `G = -56y^3 + 312y^2 - 66y + 4`.

- For `y <= 1/2`, use `-56y^3 >= -28y^2`. So `G >= 284y^2 - 66y + 4`, whose discriminant is
  `4356 - 4544 < 0`. Hence `G > 0`.
- For `1/2 <= y <= 2`, use `-56y^3 >= -112y^2`. So `G >= 200y^2 - 66y + 4`. This is increasing for
  `y >= 0.165`, and equals `21` at `y = 1/2`. Hence `G > 0`.

So `|t^k A(t)| = |A(t)| > |t + 1|` on `|t| = 1`. By Rouché, `chi_k` has no root on the circle and as
many roots in `|t| < 1` as `t^k A(t)`, namely `k + 2`. So exactly one root, `lambda`, lies outside
the closed disk. `pisot_chain_family.py` part A confirms `A(8) < 0 < A(9)`, the discriminant,
the formula for `G` and the absence of roots of `G` in `[-1, 1]` exactly.

**Step 6: irreducibility of every power.** Let `j >= 1`. The roots of `chi_{M^j}` are the `j`-th
powers of the roots of `chi_k`. So `lambda^j` is the only root outside the closed disk, and none
lies on the circle. Suppose `chi_{M^j} = g h` with monic integer `g, h` of positive degree. One of
them, say `h`, has all its roots in `|t| < 1`. Then `|h(0)| < 1`. But `h(0)` is a nonzero integer,
since `chi_{M^j}(0) = ±det M^j = ±1`. This is a contradiction.

**Step 7: fully irreducible, atoroidal, hyperbolic.**

- *Fully irreducible.* Suppose `phi^j` fixes the conjugacy class of a free factor `B` with
  `1 <= rank B <= n - 1`. Then the image of `H_1(B)` is an `M^j`-invariant direct summand of
  `Z^n` of rank `rank B`. So `chi_{M^j}` has an integer factor of that degree, contradicting
  Step 6.
- *Atoroidal.* Suppose `phi` is fully irreducible but not atoroidal. By Bestvina--Handel, `phi` is
  induced by a pseudo-Anosov homeomorphism of a compact surface `Sigma` with one boundary component
  and `pi_1 Sigma = F_n`. The characteristic polynomial does not change under a change of basis.
  - If `Sigma = N_{n,1}` is non-orientable, the boundary class `2 sum x_i` in
    `H_1 = Z^n` is nonzero and fixed up to sign. So `±1` is a root of `chi_k`. That is impossible,
    since `chi_k` is irreducible of degree `>= 4`.
  - If `Sigma = S_{n/2,1}` is orientable, `M` preserves the nondegenerate intersection form up to
    sign. So `M^2` is symplectic, and the roots of `chi_{M^2}` are closed under `z -> 1/z`. They
    would then contain as many roots outside the disk as inside, whereas `chi_{M^2}` has one root
    outside and `n - 1 >= 3` roots inside.
- *Hyperbolic.* By Brinkmann, `G_k` is hyperbolic. As a free-by-cyclic group with `n >= 2`, it is
  one-ended.

**Step 8: the surface subgroup.** The certificate of
`hyperbolic-f3-by-z-with-genus-two-surface-certificates` for `phi_1 = (a -> abb, b -> ca, c -> babb)`
is the pairing `p` in `surface_phi1028.json`, with `partial^- = {bc, BC}`. The checker rebuilds it
from `phi(b)`, `phi(c)`, the `partial^-` words and `p`:

- the `partial^-` circles `bc` and `BC`;
- the `partial^+` circles `BBABAC` and `babbca`;
- the `f`-corners at the block junctions.

`phi_k(b) = phi_1(b)` and `phi_k(c) = phi_1(c)`. So the boundary, the face and vertex permutations,
the valences `2,2,2,2,4,4`, conditions (2), (3) and (4), connectivity and `chi(X) = 6 - 8 = -2` are
literally those of `phi_1`.

Only (L) involves the gates. Every label of `X` lies in `{a, b, c, A, B, C}`. On these directions:

- `Df(a) = a` and `Df(A) = B`, because `phi_k(a)` starts with `a` and ends with `b`;
- `Df(b) = c`, `Df(c) = b`, `Df(B) = A` and `Df(C) = B`.

This is the same map as for `phi_1`, and these six directions are closed under `Df`. Two of them
share a gate iff some iterates agree, and those iterates never leave the six. So the gate relation
on the labels is that of `phi_1`, and (L) holds because it holds for `phi_1`.

By `legal-f-folded-fatgraphs-give-surface-subgroups`, `S*_f(X)` is `pi_1`-injective in `G_k`. As in
Step 4 of `hyperbolic-f3-by-z-with-genus-two-surface-certificates-proof`, it is a closed orientable
surface with `chi = -2`, so it has genus 2. For `k <= 40`, `verify_surface_rankn.py` also checks all
of this directly (`pisot_chain_family_k40.log`).

**Step 9: fibre rank is an invariant.** `H_1(G_k) = Z ⊕ coker(M - I)`, and
`|det(M - I)| = |chi_k(1)| = 28 ≠ 0`. So `b_1(G_k) = 1`, and every epimorphism `G_k -> Z` is `±`
the projection. Its kernel is `F_n`. Hence `n` is determined by `G_k`, and different `k` give
non-isomorphic groups. `QED`
