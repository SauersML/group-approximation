---
rg: 2
id: commuting-sofic-actions-need-not-combine
kind: claim
title: Commuting sofic actions need not combine to a sofic action, so GKP Question 4.2 is false
root: true
distinct_from:
  nonsofic-orbit-forces-commuting-counterexample: that is the conditional transfer principle, provable from the external toolkit alone and empty if no nonsofic action exists; this is the unconditional existence statement and additionally consumes the Kun--Thom pair
  coordinate-action-not-sofic: that is nonsoficity of a single coset action of a single group; this is nonsoficity of a combined two-group action, and it is what answers the published question
  kun-thom-nonsofic-wreath: that is the imported external theorem about wreath products over infranormal Kazhdan pairs; this is a statement about permanence of sofic ACTIONS under commuting combination, which that paper does not discuss
artifacts:
  - research/artifacts/gkp-2401-04945-verified.md
  - research/artifacts/commuting-sofic-actions-note-2026-08-17.md
---

There exist a countable group `G`, a countable set `X`, and two commuting
actions `α_1, α_2 : G ↷ X`, both sofic, whose combined action
`α : G × G ↷ X` is not sofic.

This answers **Question 4.2** of Gao–Kunnawalkam Elayavalli–Patchell,
*Soficity for group actions on sets and applications*
(arXiv:2401.04945v3 = *Res. Math. Sci.* **12** (2025), 48), verbatim:

> **Question 4.2.** Suppose we have actions `α_i : G_i ↷ X` which commute with
> each other and where `i` ranges over a countable index set. Then the actions
> naturally give rise to an action `α : ⊕_i G_i ↷ X`. `α` is sofic iff all
> `α_i` are sofic?

The forward direction is their Proposition 2.15(3) and is a theorem. The
converse is false. Their own reduction (Proposition 2.15(4)) says two groups
suffice, and the counterexample uses exactly two.

## The witness

Take the Kun–Thom pair of `kun-thom-nonsofic-wreath` Theorem E: `q` a prime
power, `r, d ≥ 3`, `R_+ = F_q[x_1,…,x_d]`, `R = F_q[x_1^{±1},…,x_d^{±1}]`,

```text
Γ = EL_r(R_+),     G = EL_r(R) ⋊ SL_d(Z),
```

`SL_d(Z)` acting by monomial substitutions. `G` is residually finite, hence
LEF, hence sofic; `Γ` is infranormal but not normal, and both have property
(T). Then on the countable set

```text
X = (G × G)/ΔΓ,        ΔΓ = {(γ,γ) : γ ∈ Γ},
```

the two coordinate actions

```text
g ·_1 (a,b)ΔΓ = (ga, b)ΔΓ,       g ·_2 (a,b)ΔΓ = (a, gb)ΔΓ
```

are commuting **free** — hence sofic — actions of `G`, while the combined
action `G × G ↷ X` is not sofic. Route:
`commuting-counterexample-from-kun-thom-pair`.

Three properties worth stating, because they close off the obvious retreats:
the combined action is **transitive**; both coordinate actions are **free**,
the most benign hypothesis available; and the acting groups are equal and
sofic. Weakening Question 4.2 by adding freeness, transitivity, or
finite-generation of the acting group does not rescue it.

## Trust surface

Two layers, and they are not the same strength.

- The transfer principle `nonsofic-orbit-forces-commuting-counterexample` uses
  only the refereed GKP paper. It is as solid as that paper.
- The *instance* additionally needs a sofic group with a nonsofic transitive
  action, i.e. `coordinate-action-not-sofic`, which rests on Kun–Thom
  arXiv:2608.06222 (v3 as of 2026-08-20; Theorems A/E hypotheses unchanged
since v1) — an unrefereed preprint two weeks old at the time of
  writing, with the trust surface recorded in
  `research/artifacts/kun-thom-2608-06222-verified.md`. If Kun–Thom Theorem A
  or Theorem E falls, this claim falls with it and the transfer principle
  survives untouched.

The group-theoretic core of the construction — freeness of both coordinate
actions for every subgroup, their commutation and combination, and the
diagonal orbit being `G/H` with stabilizer exactly `H` — is kernel-checked in
`GroupApproximation/Algebra/DiagonalCosetAction.lean`. The soficity transfers
(GKP Theorem 2.14, Propositions 2.15 and 2.16) and the Kun–Thom input are
cited, not formalized, so the claim's trust surface is exactly the two papers
above.

## Priority

A priority search on 2026-08-17 — the question text, "commuting sofic
actions", the construction, citations of the GKP paper, and work following
Kun–Thom — found no prior resolution. The Alekseev–Bradford halo-product
paper (arXiv:2601.18742), the only other systematic treatment of sofic
actions in the literature this graph tracks, states no permanence result for
commuting actions and does not mention Question 4.2. That is a priority
search, not a proof of novelty: an unindexed note or a private observation by
the authors could exist, and the construction is a two-line variation on a
paragraph in their own Section 4 (`ΔH` in place of `ΔG`), which is exactly the
kind of step an author makes without publishing it. Treat external
confirmation from Gao, Kunnawalkam Elayavalli, Patchell, Kun or Thom as
outstanding.

## Why it did not happen sooner

Not for want of the construction. GKP already run the diagonal argument on
p. 15, with `Γ ≅ (Γ × Γ)/ΔΓ` and the two multiplication actions, to show that a
positive answer to Question 4.2 would make the conjugation action of every
sofic group sofic. What was missing was any nonsofic action of a sofic group
at all — their p. 8: *"It is still open whether all actions by sofic groups
are sofic."* Kun–Thom supplied one in August 2026. The question was answerable
from the day that preprint appeared.

## Marked `root`

This is a top-level external question that the graph now closes, in the same
sense as `boone-higman-conjecture` or `whitehead-vanishing-torsion-free`. It
is not on the critical path of `q3-4-resolved`: nothing in the hyperlinear/MF
program depends on it, and it should not be wired into that cone. What it does
is convert `coordinate-action-not-sofic` from an obstruction that only closes
this repository's own routes into a fact with a published consequence.
(`goal: true` was briefly considered on 2026-08-18 and rejected: goals are
the program's open targets, and this is a closed external question — a root.)
