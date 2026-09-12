---
rg: 2
id: mixing-free-nonsofic-action-of-sofic-group
kind: claim
title: Some sofic group has a mixing free p.m.p. action that is not sofic
root: true
distinct_from:
  kun-thom-free-nonsofic-action: that is a free nonsofic action which is ergodic but never mixing, since it has the generalized Bernoulli action over G/Γ with infinite stabilizers as a factor; this asks for a mixing one, which no fixed-point-algebra argument can reach
  sofic-groups-in-paunescu-sofic-action-class: that is the refuted universal statement; this is the sharper residual question about the most chaotic actions
---

**OPEN.** There is a countable sofic group `G` and an essentially free, mixing
p.m.p. action `G ↷ (X,μ)` that is not sofic (Păunescu Definition 1.4).

## Why this is the residual question

Every nonsofic p.m.p. action of a sofic group recorded in this graph comes from
Kun--Thom Theorem C: a Kazhdan infranormal subgroup `Γ` whose fixed algebra
`L^∞(X)^Γ` is not `G`-invariant. `Γ` is infinite, so a mixing action has
`L^∞(X)^Γ = C`. Mixing passes to factors and to restrictions to infinite
subgroups, so the obstruction cannot be imported through either.
`kazhdan-fixed-algebra-blind-to-subgroup-ergodic-actions` makes this precise:
for any sofic embedding of such an action, the embedded algebra is orthogonal to
the normalized fixed algebra `D_𝒰^(σ(Γ))` beyond the constants.

A mixing counterexample would therefore need a genuinely different mechanism.
Bernoulli shifts of sofic groups are sofic (Păunescu Section 2), so it cannot be
a Bernoulli shift.

## Attempts

* **Fixed-point algebras of Kazhdan subgroups.** Dead:
  `kazhdan-fixed-algebra-blind-to-subgroup-ergodic-actions` shows Theorem C's
  conclusion holds automatically when `Γ` acts ergodically, and the algebra
  Proposition 3.1 normalizes is orthogonal to the embedded action beyond the
  constants. No contradiction can come out of that algebra.
* **Co-induction from a subgroup.** `sofic-action-class-commensurability-proof`
  transfers nonsoficity from a subgroup action to the ambient group, but it needs
  a nonsofic seed and supplies no mixing: a mixing nonsofic seed is exactly what
  is missing.
* **Permutation centralizers (Kun--Thom Theorem 4.1).** The centralizer of
  `σ(Γ)` in the universal sofic group is normalized by `σ(G)`. For a mixing
  action no nonconstant function commutes with `u_Γ`, but elements `a u_c` of the
  crossed product with `c ∈ C_G(Γ)` can. Whether Theorem 4.1 forces a condition on
  how those elements are embedded is unexplored; this is the one piece of the
  Kun--Thom machinery the blindness theorem does not cover.
