---
rg: 2
id: fpbs-tight-routes-iff-bernoulli-weakly-treeable
kind: claim
title: Bernoulli near-minimizers with uniformly tight routes and labels exist exactly when the Bernoulli action is weakly equivalent to a free treeable action
distinct_from:
  fpbs-cost-one-routes-cannot-be-uniformly-tight: that is the one-directional cost-one statement for invariant random subgraphs of a single Cayley graph, ending in amenability; this covers arbitrary graphings with unbounded label sets at every cost level, proves both directions, and ends in treeability and fixed price.
  fpbs-bernoulli-cycle-tail-compactness: that is the open cycle-tail compactness hole, equivalent to cost–Betti equality for the Bernoulli action; this is a gate showing which compactness hypothesis on near-minimizers is equivalent to weak treeability, and that it fails on every non-treeable group.
artifacts:
  - research/artifacts/fpbs-tight-routes-weakly-treeable-2026-09-17.md
---

**Setting.** Let `Γ` be an infinite group with finite symmetric generating set `S` and Bernoulli action `b` on
`([0,1]^Γ, λ^Γ)`. A graphing of `b` is a symmetric family of label sets `A_g ⊂ X` (`g ≠ e`), with edges
`{x, gx}` for `x ∈ A_g` and cost `c(Φ) = (1/2) Σ_g μ(A_g)`. A sequence `Φ_n` of graphings generating `R_b` is
near-minimizing if `c(Φ_n) → C(b)`. It satisfies **(T)**, uniform route-and-label tightness, if for every
`η > 0` there are `M` and a finite `F ⊂ Γ` such that for all `n` and `s ∈ S`, with probability at least `1−η`
the point `x` is joined to `sx` by a `Φ_n`-path of length at most `M` whose labels all lie in `F`.

**Theorem A.** The following are equivalent.

1. Some near-minimizing sequence of graphings of `b` satisfies (T).
2. There are a free p.m.p. action `a' ≺ b` and a graphing `Ψ` generating `R_{a'}` with `c(Ψ) = C(a') = C(b)`.
3. `b` is weakly equivalent to a free treeable action of `Γ`.

Under these conditions every free p.m.p. action of `Γ` has cost `C(b)`, so `Γ` has fixed price.

**Corollary B (obstruction).** If `Γ` is non-treeable, no near-minimizing sequence of graphings of `b` satisfies
(T). This applies to every infinite Kazhdan group and to every nonamenable group with a free action of cost
one. So a compactness or stability proof of `fpbs-bernoulli-cycle-tail-compactness` on such a group cannot
keep generation through a weak limit. Its near-minimizers must have routes or labels that escape with
probability bounded away from zero.

**ESTABLISHED** via `fpbs-tight-routes-iff-bernoulli-weakly-treeable-proof`. Full proof: artifact §§3–4.
The artifact also sketches Corollary B for an arbitrary free action. That extension uses a compact continuous
model of the action, which is not imported, so it is not part of this claim.
