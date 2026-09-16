---
rg: 2
id: qd-trace-positive-class-iff-k0-state-off-qd-traces-proof
kind: route
title: Sign change from the boundary theorem, then rational Hahn-Banach separation in the product of K_0-coordinates
target: qd-trace-positive-class-iff-k0-state-off-qd-traces
requires: [stw07-singular-classes-change-sign-or-sit-on-boundary]
artifacts:
  - research/artifacts/qd-trace-positive-class-k0-state-form-2026-09-16.md
---

Artifact Sections 1 and 2.

- **Preliminaries** (Lemmas 1.1 and 1.2).  `T_qd(A)` is weak* closed, by a
  diagonal choice of models with a Lipschitz bound on the multiplicativity
  defect.  It is convex, using direct sums with rational multiplicities and
  then closedness.  `r_A` is affine and continuous, and `|tau_*(g)| <= n` for
  `g = [p]-[q]` with `p, q in M_n(A)`.
- **(a) => (b).**  `A` is stably finite, being quasidiagonal, so the required
  claim gives `sigma` with `sigma_*(x) <= 0`.  By compactness `x^ >= delta > 0`
  on `T_qd(A)`.  Take an integer `N > 1/delta` and `y = Nx - [1]`.
- **(b) => (c).**  Immediate.
- **(c) => (b).**
  1. `C = r_A(T_qd(A))` is compact and convex in `R^(K_0(A))`.  Strict
     Hahn--Banach separation gives a continuous functional, which is a finite
     real combination of coordinates `s -> s(g_i)`.
  2. The bound `|s(g_i)| <= n_i` lets the coefficients be replaced by
     rationals `q_i` while keeping a gap of `delta/3`.
  3. A rational level `c` inside the gap and a common denominator `L` give
     `y = L(sum q_i g_i - c[1]) in K_0(A)`.
- **(b) => (a).**  If `my in K_0^+(A)`, then `m >= 1` contradicts
  `sigma_*(y) < 0`.  And `m <= -1` contradicts positivity on the nonempty set
  `T_qd(A)`.  So `y` is singular.
- **Extreme normal form.**  Suppose `r_A(ext T(A)) ⊆ C`.  Then
  Krein--Milman (Lemma 1.6) gives `r_A(T(A)) ⊆ C`.  So some extreme `sigma` is
  separated, and `pi_sigma(A)''` is a finite factor (Lemma 1.5, first step).
  It is not `M_k`, since otherwise `sigma = tr o pi_sigma` would be
  quasidiagonal.  For nuclear `A` it is injective with separable predual,
  hence `R` by Connes' theorem.
