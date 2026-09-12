---
rg: 2
id: leavitt-kazhdan-commutant-is-nonseparable-proof
kind: route
title: Countable saturation makes a diffuse relative commutant non-separable, and the Kazhdan commutant is of type II_1
target: leavitt-kazhdan-commutant-is-nonseparable
requires:
  - leavitt-kazhdan-relative-commutant-has-no-type-one-part
---

**Step 1: the corner is again a matrix ultraproduct.** Lift `q` to projections
`q_n in M_(d_n)` with `tr(q_n) -> tau(q) > 0`. Then `qMq` is `prod_omega q_n M_(d_n) q_n`,
with normalized traces, which is `prod_omega M_(k_n)`. The set
`S = sigma(Gamma) q` is countable, and `A_0 = S' cap qMq`.

**Step 2: separable if and only if atomic.** Let `D = S' cap N`, where
`N = prod_omega M_(k_n)`.

- **Atomic implies compact.** If `D` is purely atomic, `D = (+)_j M_(n_j)`
  with trace weights `w_j`, `sum_j w_j = 1`. Its unit ball in the 2-norm is
  the weighted `l^2` product of compact balls, which is compact because the
  tails `sum_(j>J) w_j` tend to `0`. Compact sets are separable.
- **A diffuse summand spoils compactness.** If `D` has a nonzero diffuse summand
  `zD`, it contains a Haar unitary `h` of `zD`. The powers `z h^m` are pairwise
  at 2-norm distance `sqrt(2 tau(z))`. So the unit ball of `D` is not totally
  bounded, and there is `epsilon > 0` such that every finite subset `F` of the
  ball misses some `x` in the ball with `min_(f in F) ||x-f||_2 >= 2 epsilon`.
- **Diffuse implies non-separable, by diagonalization.** Suppose `(a_i)` is a
  sequence in the ball of `D`, and fix representatives `a_i = (a_i(n))_omega`,
  `S = {s_k}`, `s_k = (s_k(n))_omega`. For each `m`, the finite-subset
  property applied to `{a_1..a_m}` gives `x in D` with the stated separation.
  So the set

  ```text
  I_m = { n : there is y in M_(k_n), ||y|| <= 1,
               ||[y, s_k(n)]||_2 < 1/m for k <= m,
               ||y - a_i(n)||_2 > epsilon for i <= m }
  ```

  belongs to `omega`. Choose `I_m` decreasing with `I_m subset [m, infinity)`.
  For `n in I_1`, let `m(n)` be the largest `m <= n` with `n in I_m`, and choose
  `y_n` witnessing it; put `y_n = 0` otherwise. Then `y = (y_n)_omega` commutes
  with every `s_k` and satisfies `||y - a_i||_2 >= epsilon` for every `i`. So
  no sequence is dense, and `D` is not separable.

**Step 3: apply it to the Kazhdan commutant.** By item 3 of
`leavitt-kazhdan-relative-commutant-has-no-type-one-part`, `A_0` has no type I
summand. So it is diffuse, and Step 2 gives `(NS)`. For `A_k`, `Ad sigma(u)^k`
is a trace-preserving automorphism of `M` carrying `A_0` onto `A_k`, so `A_k`
is non-separable as well.

Countable saturation of ultraproducts over free ultrafilters on `N` is standard
in continuous model theory (Ben Yaacov--Berenstein--Henson--Usvyatsov; Farah--Hart--Sherman).
Step 2 is written out directly so that no model-theoretic statement is imported.
