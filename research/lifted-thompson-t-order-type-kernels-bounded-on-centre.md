---
rg: 2
id: lifted-thompson-t-order-type-kernels-bounded-on-centre
kind: claim
title: Every T-bar-invariant cnd kernel on a space of finite periodic dyadic configurations of the line is bounded along the centre, and on the dyadic orbit of a point it is bounded everywhere, because translation-smearing makes it a step-function cnd on R and Riesz forces the steps to vanish
distinct_from:
  lifted-thompson-t-convex-line-walls-are-trivial: that kills measured wall structures with order-convex walls via the absence of T-invariant Radon measures on pairs; this kills every invariant cnd kernel on point-configuration spaces (walls or not, convex or not, no index measure), with a Fourier-analytic death step, and covers finitely many points per period instead of one
  thompson-t-c0-continuous-affine-actions-are-trivial: that assumes C^0-continuity of the representation; these kernels are not continuous (they jump with the winding number floor(y - x)), and continuity is not assumed but produced a.e. by the Riesz-Crum theorem along the translation flow
  lifted-thompson-t-extractable-cocycles-bounded-on-centre: that kills Koopman-type representations with a circle measure extraction; the Hilbert space of an invariant configuration kernel is a GNS space with no given measure on S^1
  lifted-thompson-t-is-a-t-menable: that is the open Haagerup question for T-bar; this kills one class of approaches to it and does not decide it
artifacts:
  - experiments/tbar-order-type-kernels-2026-09-17/check.py
  - experiments/tbar-order-type-kernels-2026-09-17/output.txt
---

**ESTABLISHED** by `lifted-thompson-t-order-type-kernels-riesz-smear-proof`
(2026-09-19, swarm-0917-w15-w15-nv-break; elementary plus the classical Riesz-Crum theorem,
not yet checked by a verifier lane).

**Setting.** `T̄` is the group of lifts to `R` of Thompson's `T`, `z(x) = x + 1`, and
`r_k(x) = x + 2^{-k}` (in `T̄`, the lift of a dyadic rotation). For `m >= 1` let `X_m` be the set
of `m`-tuples `Y = (y_1 < ⋯ < y_m < y_1 + 1)` of dyadic rationals, with `T̄` acting coordinatewise.
Say `Y` has depth `<= d` if every `y_i ∈ 2^{-d}Z`. For `Y ∈ X_m` let `H_Y ≤ T̄` be the pointwise
stabilizer of `Y + Z`.

**Theorem.**
- **(O1) One point.** Every `T̄`-invariant cnd kernel `k` on the orbit `Z[1/2] = T̄·0` is bounded:
  `k <= 4a`, where `a` is its common value on pairs at non-integral distance. Equivalently, every
  cnd function on `T̄` bi-invariant under `Stab_{T̄}(0)` (a copy of `F`) is bounded on `T̄`.
- **(O2) Configurations.** Let `k` be a `T̄`-invariant cnd kernel on `X_m` and `Y ∈ X_m` of
  depth `<= d`. Then `sup_{n ∈ Z} k(Y, z^n Y) <= 4 k(Y, r_{d+1} Y)`. Equivalently, every cnd `ψ`
  on `T̄` bi-invariant under `H_Y` satisfies `sup_n ψ(z^n) <= 4 ψ(r_{d+1})`. The same holds under
  any subgroup containing `H_Y` (for example the setwise stabilizer), and for any `T̄`-invariant
  subset of `⊔_m X_m`.
- **(O3) Sums.** Let `ψ = Σ_i ψ_i` converge pointwise, where `ψ_i` is cnd and bi-invariant under
  `H_{Y_i}` with `Y_i` of depth `<= d_i`. Then `sup_n ψ(z^n) <= 4 Σ_i ψ_i(r_{d_i + 1})`. So if
  `ψ` is proper on `⟨z⟩` then `Σ_i ψ_i(r_{d_i+1}) = ∞`, although `Σ_i ψ_i(s) < ∞` for each `s`.
  Hence `sup_i d_i = ∞`, and the mass must escape to depth: for every `D`, `Σ_{d_i <= D} ψ_i` is
  bounded on `⟨z⟩`.

**Named invariant.** The kernel is a function of the *order type* of a pair of configurations.
That type is a `Homeo~+(S^1)`-invariant, so it is unchanged by real translations `x ↦ x + t`,
which are not in `T̄`.

**Death step.** Fix `Y`. The function `φ(t) = k(Y, Y + t)` on dyadic `t` is a
translation-invariant cnd function on the translation group. It is also a step function in `t`,
with breaks only at the locally finite set `(Y − Y) + Z`. Riemann sums on generic dyadic grids
show that `e^{-sφ}` is positive definite in the integral sense for every `s > 0`. By the
Riesz–Crum theorem it is a.e. equal to a continuous function, so `φ` has no jumps and is
constant off the breaks. The winding data `floor(y − x)`, which is the only information about
`z^n` in an order type, is erased.

**Calibration.** `check.py` tests generic configurations on the dyadic orbit (`N` points per unit
length) and prints the largest eigenvalue of `P K P` on sum-zero vectors:
- a constant kernel passes;
- `ceil|x − y|`, `log`, `sqrt` and a single dip all fail once `N >= 4, 4, 8, 16` respectively;
- a single `5%` jump at distance `1` passes up to `N = 32` and fails at `N = 64`.

This matches the predicted threshold `N ≈ 1/(0.43 ε)`, where `0.43 = −min 2 sin(x)/x`. So finite
configurations only detect the obstruction at a density of order `1/ε`, which is why sparse
tests missed it.

**What is killed.** Every construction for `T̄` whose cnd function is read off pairs of finite
periodic point-configurations of the lifted line through their order type (winding numbers,
interleavings, colours), at bounded depth:
- the unit-interval metric `ceil|x − y|` and every function of `floor|x − y|`;
- walls or half-spaces spanned by configuration points, convex or not;
- Schreier-graph kernels on `T̄/H_Y`, and weighted counts of separating points;
- finite sums of any of these, and infinite sums at bounded depth.

**Forced shape of a survivor.** A cnd function proper on `⟨z⟩` must use data that is not an order
type. Examples are the dyadic affine structure (slopes, carets, as in Farley-type complexes with
parametrized intervals), or measure-class data. Otherwise it must be an infinite sum of
configuration kernels whose depths are unbounded, with `Σ_i ψ_i(r_{d_i+1}) = ∞`. The residual
quotient sums `Σ a_k ψ_k∘ι_k` of the w9 attempt on `lifted-thompson-t-is-a-t-menable` are of this
second kind when the `ψ_k` are configuration kernels, so (O3) is the quantitative test for them.
