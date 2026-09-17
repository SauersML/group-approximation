---
rg: 2
id: thompson-f-dyadic-action-is-extensively-amenable
kind: claim
title: The action of Thompson's group F on the dyadic rationals is extensively amenable
distinct_from:
  thompson-f-is-amenable: that is amenability of the group F; this is extensive amenability of one of its actions. The two are equivalent by thompson-f-amenable-iff-dyadic-action-extensively-amenable, but they are stated about different objects.
  thompson-f-end-rigid-schreier-graphs-are-amenable: that is amenability of certain Schreier graphs; extensive amenability of an action is strictly stronger than amenability of its Schreier graph in general.
artifacts:
  - research/artifacts/ideas-wildcards-2026-09-14.md
---

**OPEN.** The action of `F` on the dyadic rationals `D ⊂ (0,1)` is extensively amenable. That is, some
`F`-invariant mean on the finite subsets of `D` gives full weight to the subsets containing any given
finite set.

## Consequences

- **Co-amenability of Jones' subgroup.** Through `jones-subgroup-coamenable-if-dyadic-action-extensively-amenable`
  it gives `jones-subgroup-is-co-amenable-in-thompson-f`, answering the question in Aiello–Brothier–Conti
  Remark 4.7 positively.
- **A refutation proves F nonamenable**, by Lemma 2.1 of Juschenko–Matte Bon–Monod–de la Salle
  (`affine-lamplighter-amenable-iff-extensively-amenable`).

## Known obstacles

- **The base graph is transient.** Mishchenko (arXiv:1512.03083) shows the simple random walk on the dyadic
  Schreier graph has nontrivial Poisson boundary. So the recurrence criterion of Juschenko–Nekrashevych–de la
  Salle does not apply.
- **The action is primitive.** Point stabilizers in `(0,1)` are maximal subgroups (Aiello–Nagnibeda,
  arXiv:2103.07885, abstract). So there is no nontrivial `F`-quotient of `D` along which to apply the extension
  principle.

## Attempts

- **Inverted-orbit target (2026-09-14, hl-f-extensive-amenability-dyadic).** By JMBMdlS Proposition (§"The
  inverted orbit"), this claim is equivalent to a `μ`-independent confinement of the inverted orbit `O_n` of
  a random walk on `F`: for every `ε > 0`, `P(|O_n| < ε n) > e^{−ε n}` infinitely often, equivalently
  subexponential decay of `E(2^{−|O_n|})`, equivalently subexponential return probability of the
  switch-walk-switch walk on `(Z/2)^{(D)} ⋊ F`. This is the ESTABLISHED equivalence
  `f-dyadic-ea-iff-inverted-orbit-confinement`; the concrete OPEN target is
  `f-dyadic-inverted-orbit-is-subballistic-on-rare-events`, with route
  `f-dyadic-ea-from-inverted-orbit-confinement`.
- **The recurrence route provably fails (2026-09-14).** `f-dyadic-action-is-not-recurrent`: the mean
  inverted orbit is ballistic, `(1/n) E|O_n| → P(T = ∞) > 0`, from Mishchenko's transience. So the
  sufficient condition `(1/n) E|O_n| → 0` fails, and any proof must use the strictly weaker rare-event
  confinement. A genuine exponential upper bound on `E(2^{−|O_n|})` would instead prove `F` nonamenable.
- **Collapse onto the root (2026-09-17, swarm-0917-w4-f-decomp).** This claim is *equivalent* to
  `thompson-f-is-amenable`, by the ESTABLISHED `thompson-f-amenable-iff-dyadic-action-extensively-amenable`.
  - *Mechanism.* The breakpoint cocycle `c_g = β(g⁻¹) ∈ Z^{(D)}` embeds `F` in `Z^{(D)} ⋊ F` with trivial
    kernel. JMBMdlS Corollary "prop:functor:amenable:intro" then turns extensive amenability into
    amenability of `F`.
  - *Consequences.* The earlier distinct_from entry ("the converse is not known") was stale and is
    corrected. A refutation proves `F` nonamenable, and a proof proves `F` amenable. So
    `jones-subgroup-coamenable-if-dyadic-action-extensively-amenable` gains nothing beyond amenability of `F`.
  - *Quantitative form.* `thompson-f-dyadic-ea-witnesses-need-tower-size`: a `Γ`-invariant witness at
    level `C^{−n}` that covers the generators' breakpoints satisfies `|supp ν|·(4LC^n+3)^k ≥ exp_n(0)`. So
    witnesses of fixed tower size are excluded by Moore's theorem.
  - *Route into the root.* `thompson-f-amenable-via-dyadic-extensive-amenability`.
