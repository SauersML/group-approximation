---
rg: 2
id: lifted-thompson-t-a-t-menable-via-central-poincare-exponent
kind: route
title: "One cnd function on T-bar with zero Poincare exponent along the centre gives, through a dissipative Gaussian action, a measurable Euler splitting and hence Haagerup for T-bar"
target: lifted-thompson-t-is-a-t-menable
requires:
  - lifted-thompson-t-has-cnd-with-zero-central-poincare-exponent
  - central-zero-poincare-exponent-gives-euler-splitting
  - central-extension-haagerup-from-measurable-euler-splitting
  - thompson-v-has-haagerup-property
---

**Not the (MT) route.** `lifted-thompson-t-a-t-menable-via-measurable-euler-splitting` asks for a
measure space directly. This route replaces the space by a growth condition on a single cnd
function along one cyclic subgroup. The space is then built by
`central-zero-poincare-exponent-gives-euler-splitting` (established).

**Route.**
1. `lifted-thompson-t-has-cnd-with-zero-central-poincare-exponent` gives `ψ` on `T̄` with
   `δ_z(ψ) = 0`.
2. `central-zero-poincare-exponent-gives-euler-splitting` gives a nonsingular `T`-space `W` with
   almost invariant Koopman vectors and an integer splitting `β`, `β(z, ·) = 1`. That is (MT).
3. `central-extension-haagerup-from-measurable-euler-splitting`, with `T` Haagerup by
   `thompson-v-has-haagerup-property` (restrict from `V`), gives `T̄` Haagerup.

**Tightness.** The target implies that some `ψ` is proper on `⟨z⟩`. Prerequisite 1 asks for
superlogarithmic growth instead. In spectral terms (see that node), properness needs
`Σ_k c_k = ∞` for the dyadic masses of `b(z)` under `π(z)`, and prerequisite 1 needs at least `sup_k c_k = ∞`.
Apart from this rate along `⟨z⟩`, nothing separates the route from the target.

**Where it sits in `brin-thompson-groups-nv-are-a-t-menable`.** `T̄ ≤ 2V`, so the Haagerup property of
`T̄` is necessary for the goal at `n = 2`. This route gives the sharpest known sufficient condition for
that necessary piece.

**Attack order.**
1. Test the known cnd functions of `T̄` (none recorded that are unbounded on `⟨z⟩`) against the
   dyadic-mass test `sup_k c_k = ∞`.
2. Try to refute: a proof that every cocycle of `T̄` has bounded dyadic masses `c_k`. This would be a
   quantitative relative-(T) statement. It would leave the target open.
