---
rg: 2
id: fpbs-countable-groups-have-fixed-pseudocost
kind: claim
title: All free actions of each countably infinite group have the same pseudocost
distinct_from:
  fpbs-fixed-price-universal: that asks all free costs to agree; this asks only that all pseudocosts agree, which excludes shape (A) but not an infinite free cost at a group of finite cost (shape (B)).
  fpbs-relative-sandwich-cost-bernoulli-lower-bound: that is a relative comparison on finitely generated groups which implies this; this is the pseudocost statement for arbitrary countable groups.
  fpbs-locally-free-free-action-costs-are-c-star-or-infinite: that establishes this statement for locally free groups whenever some free cost is finite; this is the statement for all countably infinite groups.
artifacts:
  - research/artifacts/fpbs-sandwich-cost-quantifier-shift-2026-09-17.md
  - research/artifacts/fpbs/docs/fixed-price-countable-passage.md
---

**OPEN.** Let `Γ` be a countably infinite group. Prove that every free p.m.p.
action `a` of `Γ` satisfies `PC(a) = PC(s_Γ)`, where `PC` is Tucker-Drob's
pseudocost.

**What is known.** By Abért–Weiss and Tucker-Drob Cor 6.20, `PC(a) ≤ PC(s_Γ)`
always holds. So the content is `PC(s_Γ) ≤ PC(a)`.

**Why it matters.**
- With `fpbs-finite-cost-groups-free-actions-have-finite-cost`, it gives
  `fpbs-fixed-price-universal`, via route
  `fpbs-fixed-price-from-fixed-pseudocost-and-finite-costs`.
- It follows from the finitely generated statement
  `fpbs-relative-sandwich-cost-bernoulli-lower-bound`, via route
  `fpbs-fixed-pseudocost-from-relative-sandwich-bound`.
- The flagship implies it for groups with `C(Γ) < ∞`.

**How it can fail.** A counterexample `Γ` has free actions with different
pseudocosts. By `fpbs-pseudocost-localizes-to-fg-sandwich-costs`,
`PC(a) = sup_F inf_{Δ ⊇ F} p^Δ_F(a|Δ)`. So there are:
- a finite `F ⊆ Γ`;
- a free `a`;
- a finitely generated `Δ_0 ⊇ F` in `Γ`,

with `p^{Δ_0}_F(a|Δ_0) < p^{Δ'}_F(s_{Δ'})` for every finitely generated
`Δ' ⊇ F` in `Γ`. In particular, RBL fails at `(Δ_0, F, a|Δ_0)`. If
`C(Γ) < ∞`, this is shape (A) of Theorem G of the passage artifact.

## Attempts

**Localization to finitely generated subgroups (September 17, 2026, b-t-nonamgen).**
- Tried: write `PC(a)` as `sup_F inf_Δ p^Δ_F(a|Δ)` and `PC(s_Γ)` as
  `sup_F inf_Δ p^Δ_F(s_Δ)`, using `s_Γ|Δ ≅ s_Δ`
  (`fpbs-pseudocost-localizes-to-fg-sandwich-costs`). Then compare the two
  pointwise in `(Δ, F)`.
- Where it stops: the pointwise comparison is exactly
  `fpbs-relative-sandwich-cost-bernoulli-lower-bound`. Nothing about `a|Δ`
  beyond freeness is available, because a restricted free action is an
  arbitrary free action of `Δ`. So this reduction is lossless at the level of
  the argument, and it moves the whole difficulty to the finitely generated
  statement.
- Not usable: the pointwise bound for `F` generating `Δ` alone, that is fixed
  price for finitely generated groups. The infimum runs over `Δ ⊇ F`, and it
  can be approached along subgroups where `F` does not generate.
