---
rg: 2
id: thompson-f-amenable-via-costly-ramsey-amplification
kind: route
title: Show that Ramsey amplification in F needs unbounded tower overhead; finiteness of the Ramsey function then gives amenability
target: thompson-f-is-amenable
requires:
  - thompson-f-ramsey-amplification-needs-unbounded-tower-overhead
  - moore-ramsey-criterion-for-amenability
---

**Route.** Assume `thompson-f-ramsey-amplification-needs-unbounded-tower-overhead`. For each `D` it gives `m_D, u_D`
with a strict inequality whose right side `exp_D(R(exp_D(m_D+u_D)) + u_D)` must be finite. So
`R(exp_D(m_D+u_D)) < ∞`, and `exp_D(m_D+u_D) ≥ exp_D(1)` is unbounded in `D`. By the monotonicity facts in
`moore-ramsey-criterion-for-amenability`, `R` is nondecreasing, so `R(M) < ∞` for every `M`. Every finite `A ⊆ F`
lies in some ball `B_M`, and `B_{R(M)}` is 1/2-Ramsey with respect to `A` by monotonicity in `A`. Theorem 1.3
(2)⇒(4) gives that `F` is amenable.

**Why this is a decomposition and not a renaming.** The prerequisite is strictly stronger than the target: it also
asserts that the nested-Ramsey composition in (3⇒4) of Moore's Theorem 2.1 cannot be replaced by a bounded tower in
`F`. It fails on its own if AMP(D) holds for some `D`, whether or not `F` is amenable. By Proposition D of
`thompson-f-ramsey-function-iterates-reach-towers`, it is exactly the condition that an elementary Ramsey function
for `F`, which is Moore's "moderate rate" hope, needs. So this route isolates the one quantitative bet that
separates the Ramsey program from building Følner sets directly.
