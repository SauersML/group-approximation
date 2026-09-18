---
rg: 2
id: f-dyadic-inverted-orbit-is-subballistic-on-rare-events
kind: claim
title: The inverted orbit of a random walk on Thompson's F acting on the dyadic rationals is confined to o(n) points on events of only subexponentially small probability
distinct_from:
  f-dyadic-action-is-not-recurrent: that says the mean inverted orbit is ballistic, an established fact; this is the strictly weaker rare-event confinement, which is open and would prove extensive amenability.
  thompson-f-dyadic-action-is-extensively-amenable: that is extensive amenability of the dyadic action; this is its concrete probabilistic form via the inverted orbit, equivalent to it by f-dyadic-ea-iff-inverted-orbit-confinement.
artifacts:
  - research/artifacts/hl-f-extensive-amenability-dyadic-2026-09-14.md
---

**OPEN.** Let `μ` be a non-degenerate symmetric finitely supported probability measure on `F` with
generating support, `x_0 ∈ D`, `g_n = h_n⋯h_1` the left random walk, and
`O_n = {x_0, g_1⁻¹x_0, …, g_n⁻¹x_0}` the inverted orbit. Then for every `ε > 0`,

`P(|O_n| < ε n) > e^{−ε n}` for infinitely many `n`.

Equivalently, `E(2^{−|O_n|})` decays subexponentially. By `f-dyadic-ea-iff-inverted-orbit-confinement` this
does not depend on `μ` or `x_0`.

**Status of the two directions.**
- A proof of this claim gives `thompson-f-dyadic-action-is-extensively-amenable`
  (`f-dyadic-ea-from-inverted-orbit-confinement`), hence co-amenability of Jones' subgroup
  (`jones-subgroup-is-co-amenable-in-thompson-f`), answering Aiello–Brothier–Conti Remark 4.7 positively.
- A refutation — a genuine exponential upper bound `E(2^{−|O_n|}) ≤ e^{−cn}`, equivalently exponential decay
  of the switch-walk-switch return probability on `(Z/2)^{(D)} ⋊ F` — proves `F` is not amenable.

**Why it is hard.** The mean is ballistic, `(1/n) E|O_n| → P(T=∞) > 0`
(`f-dyadic-action-is-not-recurrent`), so the confinement is a large-deviation statement: the trajectory
of the inverse walk must, with only subexponentially small probability, stay confined to a vanishing
fraction of the dyadics it would typically escape through. This is a spectral-radius / cogrowth question
for the dyadic lamplighter, of the same order of difficulty as the unsettled cogrowth numerics for `F`
itself (recorded in `research/artifacts/ideas-wildcards-2026-09-14.md`).

## Attempts

- **Last-mile audit, then a rate kill (2026-09-17, swarm-0917-w6-w6-f-last2, quantifier-shift).**
  - *Closest route.* This hole is the only open prerequisite on `thompson-f-amenable-via-dyadic-extensive-amenability`,
    the route into `thompson-f-is-amenable` with the fewest open prerequisites. But it is equivalent to the root
    (`thompson-f-amenable-iff-dyadic-action-extensively-amenable`), so "last missing" here means the root itself.
  - *Second route.* `thompson-f-amenable-via-exotic-co-amenable-subgroup` has two open prerequisites, and its first
    one refutes the Brin–Sapir conjecture. Every sandwich split collapses by
    `f-sandwich-splits-collapse-unless-kernel-is-brin-sapir-exotic`, and algebraic EA certificates die by
    `f-ea-calculus-certificates-force-f-prime-to-act-trivially`. So no route is closer than the analytic target.
  - *Established,* `f-dyadic-confinement-witness-times-match-folner-function`. Let `e ∈ supp μ`, and let
    `N_μ(ε)` be the least `N` with `P(|O_N| < εN) > e^{−εN}`. Then
    `log₂ Føl_Γ(1/η) / O(log²(1/η)) ≤ N_μ(ε)` whenever `ε ≤ η²/polylog(1/η)`, and `N_μ(ε) ≤ 2⌈4 Føl_Γ(8/ε)/ε⌉`.
    - *Lower bound.* An almost invariant lamp law `f²` comes from a good return ratio of the switch-walk-switch
      chain. Conjugated switches and unions of independent lamp sets make it a breakpoint-covering measure. The
      box and cocycle push of `thompson-f-dyadic-ea-witnesses-need-tower-size-proof` turns that into a Følner set.
    - *Upper bound.* A Følner set `U` lifts to `{(φ,g) : g ∈ U, supp φ ⊆ Ux_0}` in the lamplighter, and a spectral
      lower bound on its return probability follows.
    - *Credit.* The Moore instance, tower-size witness times, was obtained independently by swarm-0917-w6-w6-f-last1
      (`f-dyadic-inverted-orbit-confinement-needs-tower-times`, uniform `μ` at the root `1/2`). This node answers that
      sibling's spark about the tetration survivor band.
  - *Invariant.* The witness-time function `N_μ(ε)`, compared with `log Føl_Γ`.
  - *Class killed.* Passing to this hole in order to get a target quantitatively cheaper than Følner sets. Every
    certified witness time is a certified Følner bound one exponential up (Step 5 of the proof). So effective
    confinement proofs, and trap strategies bounded by a fixed tower, die against Moore's bound.
  - *Dies at / survives.* The hole stays OPEN. The survivor band is exactly the Følner band: if `F` is amenable,
    `N_μ(ε) ≤ Føl_Γ(8/ε)/ε`. So the hole is quantitatively the Følner problem, and no reduction through it can buy
    more than one exponential.

- 2026-09-17, swarm-0917-w6-w6-f-last1 (family probability-random): quantitative class kill, the hole stays OPEN.
  The spectral route `f-dyadic-inverted-orbit-confinement-needs-tower-times-proof` works for `μ` uniform on
  `{e, x_0^{±1}, x_1^{±1}}` and `x_0 = 1/2`. Take a good return ratio of the switch-walk, project onto
  root-switch invariant functions, take a union of `r` samples, and apply
  `thompson-f-dyadic-ea-witnesses-need-tower-size`. This proves
  `f-dyadic-inverted-orbit-confinement-needs-tower-times`:
  - `E 2^{−|O_{2n}|} ≤ exp(−n C^{−2 log* n − O_C(1)}/O_C((log* n)²))` at every time;
  - the first `N` with `P(|O_N| < εN) > e^{−εN}` is at least a tower of height about `½ log_C(1/ε)`.
  Invariant: Moore's Følner tower, carried to finite dyadic sets by the breakpoint cocycle. Dying step: exhibiting
  the confinement time `n(ε)` or the lower-bound profile. Explicit times of bounded tower height die there, and so
  do profiles `exp(−n/g(n))` with `log g/log* n → ∞`, including stretched exponentials. The hole itself needs only
  a vanishing rate, and item 2 allows rates `C^{−2 log* n}`, so nothing here decides it.
