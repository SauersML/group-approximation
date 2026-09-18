---
rg: 2
id: kt-compressor-stable-kernel-overgroups-are-polynomial
kind: claim
title: A Mon-stable subgroup of SL_r(Laurent) containing SL_r(polynomial) with polynomial root contents has polynomial entries
distinct_from:
  kt-compressor-stable-polynomial-content-overgroups-are-gamma: that allows elements with nontrivial SL_d(Z) projection; this is the kernel case, which is equivalent to it by kt-compressor-sandwich-equivalent-to-kernel-polynomiality
  kt-compressor-stable-overgroups-have-polynomial-content: that controls the root subgroups; this asks for control of all entries
artifacts:
  - experiments/root-free-overgroups-2026-09-17/root_extraction.py
---

**OPEN.** Let `A = F_q[x_1,…,x_d] ⊂ R = F_q[x_1^(±1),…,x_d^(±1)]`, `r,d ≥ 3`, and
`Mon = SL_d(Z) ∩ M_d(N)` acting on `R` by `x^v ↦ x^(Pv)` and entrywise on matrices. Let
`H ≤ SL_r(R)` with

```text
SL_r(A) ≤ H,     P·H ≤ H for all P ∈ Mon,     H ∩ U_12(R) = U_12(A).
```

Then `H = SL_r(A)`.

By `kt-compressor-sandwich-equivalent-to-kernel-polynomiality` this is equivalent to
`kt-compressor-stable-polynomial-content-overgroups-are-gamma`, and so it closes the route
`kt-pair-floor-reduces-to-wreath-model-via-compressor-sandwich`.

## What is known

* **(Dichotomy.)** The `A`-span of the entries of `H` is `A` or `R`, so a counterexample
  has entries spanning all of `R` while every root element stays polynomial.
* **(One variable.)** For `d = 1` the analogue holds with no stability hypothesis:
  `SL_r(F_q[t])` is a maximal subgroup of `SL_r(F_q[t^(±1)])`, by density in
  `SL_r(F_q((t)))`.
* **(Dead candidates.)** Lattice and semilinear lattice stabilizers give nothing new. An
  `SL_r(A)`-stable `A`-submodule of `R^r` is `I^r`, its stabilizer is `SL_r(O(I))`, and
  the root content of that is the multiplier ring `O(I)`. Row-type unipotents
  `I + e_k u^T` with a non-polynomial entry have a non-polynomial root element after one
  commutator with `e_(mn)(1)`. Monomial and torus elements with nonconstant entries
  conjugate `U_ij(A)` outside `A`.

## Where a proof must use the compressors

For `d ≥ 2` no valuation ring meets `R` in `A`, so the one-variable density argument only
gives `H·SL_r(R ∩ O_ν) = SL_r(R)` for the valuations `ν` that `H` moves. Transvections
`h e_ij(a) h^(-1) = I + a·(he_i)(e_j^T h^(-1))` lie in `H`. Splitting them into elementary
matrices needs coefficients in `R`, which `H` does not contain.

## Attempts

* **2026-09-18 (swarm-0917-w7-w7-nh-follow): resolved, and no compressors are needed.**
  Route `kernel-polynomiality-from-no-root-free-overgroup`, through
  `sl-r-polynomial-has-no-root-free-laurent-overgroup`, with proof route
  `sl-r-polynomial-no-root-free-laurent-overgroup-proof` (`requires: []`). The statement
  holds for every `d >= 1` and every `H` with `E_r(A) <= H <= SL_r(R)` and
  `H ∩ U_12(R) = U_12(A)`. It holds more generally for `A` a UFD and `R = A[1/f]`.
  The objection above, that transvections cannot be split, is bypassed as follows.
  - For `τ = h e_ij(1) h^(-1) = 1 + uw`, put `q = μw` (polynomial, with `μ` a
    monomial) and `v = q_b e_a - q_a e_b`, a Koszul syzygy of `w`.
  - Then `1 + v e_k^T` is in `E_r(A)`, and
    `[e_nk(1), [τ, 1 + v e_k^T]] = 1 + u_k w_n v e_k^T` is a single-column unipotent in `H`.
  - One more commutator gives the root `e_ck(u_k w_n q_b)`, so `u_k w_n q_a in A`.
  - Conjugate by `γ in E_r(A)` so that all coordinates of `w` have the same `x_i`-adic
    valuation. Then `h E_ij h^(-1) in M_r(A)` for all `i != j`, and a min-valuation
    count gives `h in SL_r(A)`.
  - There is no diagonal case, because after normalisation the valuation of `N_(kn)`
    does not depend on `n`.
  - Certificate: `experiments/root-free-overgroups-2026-09-17/root_extraction.py`
    evaluates the explicit word on random non-polynomial `h`. All runs pass.

  The "Where a proof must use the compressors" section above is superseded.
* **Resolved (w5-121): proved, via `kt-kernel-overgroups-polynomial-via-vertex-compressors-proof`.**
  The compressor is chosen after the column. For a column `u = he_i` of `h ∈ H` and a bad
  exponent `m` of `uv^T` with `m_(i0) < 0`, pick `P ∈ Mon` whose rows all lie in one open
  normal cone of `conv(∪ supp u_k)`, at a vertex `m*`, and all lie close to `e_(i0)`.
  Then `x^(−Pm*)·P·u` is `A`-unimodular: on the torus because `u` is `R`-unimodular, and on
  every coordinate hyperplane because only the `m*` monomial survives. By
  Quillen–Suslin and zero-entry extraction, `P·(uv^T) ∈ M_r(A)`. But `Pm` is negative in
  every coordinate, a contradiction. So every conjugated transvection is polynomial, and
  `H = SL_r(A)` by the transvection criterion. This uses one `P` per bad exponent, which
  avoids the cone gap `∩ P^(-1)(N^d) ⊋ N^d` of the fixed-shape compressors `I + kE_21`.
  It also treats the Koszul-type columns `(x_1,x_2,x_3)` like any other column. In `d = 1`,
  where `P = 1`, it reproves the maximality calibration.
* **Referee check (w6-121): Lemma 2 and step 5 pass.** Lemma 2: on `V` one has
  `⟨ρ,m⟩ ≤ |ρ|(m_(i0) + ε|m|) < 0` since `m_(i0) ≤ −1`; `C` is `V` cut by finitely many strict
  inequalities, so an open cone with a primitive integer point `w`; adding `N·w` to the other
  basis rows keeps determinant `1`, and `(b_k + Nw)/N → w` puts every row in `C ⊂ R^d_(>0)`, so
  `P ∈ M_d(N)`. Step 5: `P` acts by the ring automorphism `x^m ↦ x^(Pm)` of `R`, which is
  `F_q`-linear and bijective on exponents, so `(P·Y)_(ab)` has the monomial `x^(Pm)` with the
  same coefficient, and `P·Y = (P·u)(P·v)^T`. Steps 2-4 also check (`X^2 = 0`, `y_r = 0`,
  `P·Y = g^(-1)e_r y^T g`), and the transvection criterion is Skolem–Noether with
  `det h = 1` killing the monomial unit. No gap found. The body still reads **OPEN**; the
  graph derives ESTABLISHED through the w5-121 route.
