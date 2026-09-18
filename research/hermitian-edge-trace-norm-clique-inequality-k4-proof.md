---
rg: 2
id: hermitian-edge-trace-norm-clique-inequality-k4-proof
kind: route
title: Gauge to a flux torus, dualise the trace norm for fixed phases, and cover the torus by boxes carrying exact rational SDP-dual certificates
target: hermitian-edge-trace-norm-clique-inequality-k4
requires: []
artifacts:
  - experiments/hermitian-edge-trace-norm-clique-small-m-2026-09-18/cliquebb.py
  - experiments/hermitian-edge-trace-norm-clique-small-m-2026-09-18/README.md
  - experiments/hermitian-edge-trace-norm-clique-small-m-2026-09-18/k4_full_torus.log
---

This is a computer-assisted proof. The mathematical reduction is below, and the machine part is an
interval branch-and-bound whose certificates are checked in exact rational arithmetic. It is
unreviewed and not Lean-verified. Lane w6-078, 2026-09-18. Script:
`experiments/hermitian-edge-trace-norm-clique-small-m-2026-09-18/cliquebb.py`.

**Theorem.** Every Hermitian `4 x 4` matrix `K` with `K_ii = 0` and `|K_ij| >= 1` (`i != j`) has
`||K||_1 >= 3 sqrt3`. (The numerical minimum is `2 + 2 sqrt3 = 5.464`, against `3 sqrt3 = 5.196`.)

Steps 1–4 are written for general `m`, because the same script handles `m = 5`.

## Step 1. Gauge

Conjugation by a diagonal unitary `U` preserves `||K||_1`, the diagonal and all moduli. Choosing
`U_11 = 1` and `U_jj = conj(K_1j)/|K_1j|` makes `K_1j = t_1j >= 1` real for `j >= 2`. Write the remaining
entries as `K_ij = t_ij e^{i theta_ij}` (`2 <= i < j`), with `t_ij >= 1`. The free phases
`theta in [0, 2 pi)^F` have `F = 3` for `m = 4` and `F = 6` for `m = 5`.

## Step 2. Large moduli

For `i != j`, let `P` be the projection onto `span(e_i, e_j)`. Compression does not increase the trace
norm, so `||K||_1 >= ||PKP||_1 = 2|K_ij|`. Put `T = 2.6` for `m = 4` and `T = 3.47` for `m = 5`. Then
`2T > sqrt3 (m-1)` (`5.2 > 5.196`, `6.94 > 6.928`). So we may assume `t_ij <= T` for every pair.

## Step 3. A certificate for one box

Let `Z` be Hermitian with `-I <= Z <= I`. Then `||K||_1 >= tr(ZK)`, and

```text
tr(ZK)  =  sum_{i<j} t_ij g_ij(theta_ij),        g_ij(theta) = 2 Re( Z_ji e^{i theta} )
```

with `theta_1j = 0`. For `t in [1, T]`, `min_t t g` is `g` if `g >= 0` and `T g` if `g < 0`. The
right-hand side is a sum of functions of single variables `(t_ij, theta_ij)`. So its minimum over a box
`B = prod_ij [a_ij, b_ij]` of phases, and over `t in [1, T]^E`, is the sum of the per-edge minima. Each
per-edge minimum is `2|Z_ji|` times the minimum of a cosine over an interval, which is computed
exactly and then padded outward. Hence, if

```text
L(Z, B)  :=  sum_{i<j}  min_{theta in [a_ij, b_ij]}  min_{t in [1,T]}  t g_ij(theta)   >=  sqrt3 (m-1),
```

the theorem holds for every `K` whose phases lie in `B`.

## Step 4. Covering the torus

Branch-and-bound runs over boxes. For each box it first tries the parent's certificate. Otherwise it
solves, at the centre `theta_0`, the SDP

```text
max  sum_{i<j} g_ij(theta_0)   s.t.  -I <= Z <= I,  g_ij(theta_0) >= 0 ,
```

which is the dual of `min_{t >= 1} ||K(theta_0, t)||_1`. The optimiser `Z` is scaled by `1 - 10^{-6}`,
rounded to Gaussian rationals with denominator `2^30`, and made exactly Hermitian. `I - Z` and `I + Z`
are then checked positive definite in exact `Fraction` arithmetic: all pivots of an unpivoted `LDL*`
elimination must be positive. The box is closed if `L(Z, B) >= sqrt3 (m-1)`; otherwise it is bisected
along its widest side. Neighbouring boxes share float endpoints, and every per-edge phase interval is
widened by `10^{-12}`, so the closed boxes cover the torus. The SDP solver is not trusted. Only the
exact positive-definiteness check and the padded evaluation of `L` enter the proof.

**m = 4** (`k4_full_torus.log`). The whole torus `[0, 2 pi)^3` is covered with no symmetry reduction,
using 584 boxes and 740 SDP solves. The smallest half-width is `0.196`. The smallest SDP value at a
box centre is `5.502`. The global minimum `2 + 2 sqrt3 = 5.464` is attained at flux
`(2pi/3, 2pi/3, 2pi/3)` (grid scan).

**m = 5.** The same script with `m = 5` runs over the six-dimensional torus. It uses the symmetries
`C -> -C` (followed by conjugation with `diag(-1,1,1,1,1)`, which shifts every free phase by `pi`) and
`C -> conj C` (which negates them) to restrict the first free phase to `[0, pi/2]`. That run is in
progress and is not claimed here.

## Why the certificates are coarse

At a minimiser `theta*` of `v(theta) = min_t ||K(theta,t)||_1`, the envelope theorem makes each
`g_ij'(theta*_ij)` vanish. So a fixed certificate loses only to second order in the box size, exactly
where the margin `v - sqrt3 (m-1)` is smallest. Because the certificate is separable, `L(Z, B)` is its
exact minimum over the box, so no dependency loss occurs.
