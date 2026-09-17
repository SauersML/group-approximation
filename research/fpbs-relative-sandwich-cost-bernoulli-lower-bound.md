---
rg: 2
id: fpbs-relative-sandwich-cost-bernoulli-lower-bound
kind: claim
title: For finitely generated groups the Bernoulli shift minimizes every relative sandwich cost among free actions
distinct_from:
  fpbs-free-action-cost-at-least-bernoulli-cost: that is the case where F generates Delta, so the sandwich cost is the cost C(a) and the statement is fixed price for finitely generated groups; this asks the same inequality for every finite F, including F generating a proper subgroup, and so implies that one.
  fpbs-countable-groups-have-fixed-pseudocost: that is fixed pseudocost for all countable groups; this is a statement about finitely generated groups only, and implies that one through fpbs-fixed-pseudocost-from-relative-sandwich-bound.
artifacts:
  - research/artifacts/fpbs-sandwich-cost-quantifier-shift-2026-09-17.md
---

**OPEN.** For a countable group `Δ`, a p.m.p. action `a` of `Δ` and a finite
`F ⊆ Δ`, let

    p^Δ_F(a) = inf { C(E) : E_{a|⟨F⟩} ⊆ E ⊆ E_a }.

Let `s_Δ` be the Bernoulli shift `[0,1]^Δ`. Prove: for every finitely
generated group `Δ`, every finite `F ⊆ Δ` and every free p.m.p. action `a` of
`Δ`,

    p^Δ_F(s_Δ) ≤ p^Δ_F(a).

**Why it matters.**
- **Case `F` generates `Δ`.** Then `p^Δ_F = C`, and the statement is
  `fpbs-free-action-cost-at-least-bernoulli-cost`. With Abért–Weiss
  maximality, that is fixed price for finitely generated groups.
- **All `F`.** The statement gives fixed pseudocost for every countably
  infinite group (`fpbs-fixed-pseudocost-from-relative-sandwich-bound`). That
  excludes shape (A) of Theorem G of the passage artifact everywhere, using
  only finitely generated groups.

**Reverse inequality.** For infinite `Δ`, the reverse inequality
`p^Δ_F(a) ≤ p^Δ_F(s_Δ)` follows from Abért–Weiss and Tucker-Drob's openness
theorem (artifact Proposition 2.5, not a graph node). So the statement is
equivalent to: `p^Δ_F` is constant on free actions of `Δ`.

**Known cases** (artifact §3, remarks):
- finite `Δ`;
- amenable `Δ`, where the infimum is attained at `E_{a|⟨F⟩}` and depends only
  on `|⟨F⟩|`.

**First test.** `Δ = F_2`, with `F` generating a free subgroup of infinite
index and rank at least 2. All sandwich relations are treeable.

**Open question.** Does fixed price for all countable groups imply this
statement?

## Attempts

**Openness plus weak containment (September 17, 2026, b-t-nonamgen).**
- Tried: use that `A_{F,r}` is open in the weak topology at free actions
  (`tucker-drob-sandwich-sets-open-at-free-actions`) and that `s_Δ` is weakly
  contained in every free `a` (Abért–Weiss).
- Where it dies: openness of `{p_F < r}` makes `p_F` upper semicontinuous.
  Every free `a` has `s_Δ` in the closure of its conjugacy class, so the argument
  moves small sandwich cost from `s_Δ` to `a`. That gives only the reverse
  inequality `p^Δ_F(a) ≤ p^Δ_F(s_Δ)`. No lower semicontinuity of `p_F` is known,
  and at `F` generating `Δ` it would be fixed price for `Δ`.
- Deferred: the `F_2` test above. There every sandwich relation is treeable,
  but a treeable `E` with `E_{a|⟨F⟩} ⊆ E ⊆ E_a` has no generating free action
  to which Gaboriau's fixed price applies. So the test needs a direct cost
  computation for intermediate treeable relations, which was not attempted.
