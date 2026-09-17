---
rg: 2
id: thompson-f-interval-avoiding-walks-have-positive-entropy
kind: claim
title: A finite-entropy step distribution on Thompson's group F whose induced dyadic chain avoids a support interval with positive probability has positive asymptotic entropy, so it is not Liouville
distinct_from:
  thompson-f-finite-breakpoint-moment-walks-are-not-liouville: that kills measures with finite expected breakpoint count by stabilizing lamps through a Green-function bound; this assumes only finite entropy and an avoidance event of the induced chain, and proves positive entropy by an information count of conjugated bump insertions. No breakpoint moment appears.
  thompson-f-random-walks-are-not-liouville: that imports non-Liouville for finitely supported strictly non-degenerate measures; this is a conditional positive-entropy criterion for infinitely supported finite-entropy measures.
  thompson-f-dyadic-orbit-walks-are-transient: that is transience of the induced chain on points; this uses a real-topology avoidance property of the same chain, which transience does not give.
---

**ESTABLISHED.** Notation: `D` is the set of dyadic rationals in `(0,1)`. For a probability measure `µ` on `F`, the
*induced chain* started at `z ∈ D` is `Z_0 = z`, `Z_k = h_k(Z_{k−1})` with `h_k` i.i.d. of law `µ`. This is the
chain `x ↦ h(x)` of `thompson-f-dyadic-orbit-walks-are-transient`.

**Theorem (interval avoidance gives entropy).** Let `µ` be a probability measure on `F` with `H(µ) < ∞`. Assume
there are

- an element `b ≠ e` in `∪_{k≥1} supp µ^{*k}` with convex hull of `supp b` equal to `[x,y] ⊂ (0,1)`, and
- positive probability that the induced chain from `x` never enters `[x,y]`: `θ := P_x(Z_k ∉ [x,y] for all k ≥ 1) > 0`.

Then the lazy measure `λ = (µ + δ_e)/2` has asymptotic entropy `h(λ) > 0`. By the entropy criterion, `µ` is not
Liouville.

If `sgr supp µ = F`, the first condition holds for every dyadic `x < y` in `(0,1)`: take for `b` a copy of `x_0` on
`[x,y]`. So for generating `µ` the hypothesis is only that the induced chain from some dyadic `x` avoids some
`[x,y]` with positive probability.

**Corollary (what a finite-entropy Liouville witness must do).** Let `µ` have `H(µ) < ∞`, `sgr supp µ = F`, and
suppose `µ` is Liouville. Then for every start `z ∈ D` and every `x ∈ D`, almost surely `x` is a limit from the
right of the induced chain's path: `inf{Z_k − x : Z_k > x, k ≥ K} = 0` for every `K`. So the chain is transient
on points (by `thompson-f-dyadic-orbit-walks-are-transient`), yet its path is dense and approaches every dyadic
from the right infinitely often.

Proof: `thompson-f-interval-avoiding-walks-positive-entropy-proof`.
