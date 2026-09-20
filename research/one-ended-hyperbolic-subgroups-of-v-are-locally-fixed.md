---
rg: 2
id: one-ended-hyperbolic-subgroups-of-v-are-locally-fixed
kind: claim
title: A one-ended hyperbolic subgroup of Thompson's V fixes a neighborhood of every point by a nontrivial element; torsion-free ones have no north–south elements
distinct_from:
  topologically-free-fg-subgroups-of-v-are-virtually-free: that leaves a countable exceptional set K of points with cyclic stabilizers; this proves K is empty for one-ended hyperbolic groups, via Lemma L below.
  raag-subgroups-of-v-contain-no-one-ended-hyperbolic-group: that only excludes the RAAG route; this constrains every embedding of a one-ended hyperbolic group in V.
  cyclic-centralizer-subgroups-of-nv-have-meeting-supports: that gives meeting supports for groups with cyclic centralizers; this adds that every point is interior-fixed, and combines the two to exclude north–south dynamics.
artifacts:
  - research/artifacts/gq-bh-scout-bbmz-ranked.md
---

**ESTABLISHED** by `one-ended-hyperbolic-subgroups-of-v-locally-fixed-proof` (lane proof, bh-scout-bbmz, 09-19).
Refereed PASS by bh-ref-t0 after an adversarial check, at 020fc76108
(`research/one-ended-hyperbolic-v-locally-fixed-review.md`). Every step passes: the Schreier-graph identification,
the lifted geodesics, the (E3) height argument (the use of `ξ ∉ Hη` is essential), and items 1–2. It builds on `topologically-free-fg-subgroups-of-v-are-virtually-free`, which rests on
Hyde–Skipper–Zaremsky arXiv:2605.20564v2, Theorem A.

**Lemma L.** Let `Γ` be a hyperbolic group, `c ∈ Γ` of infinite order with fixed points `c^±` in `∂Γ`, and suppose
`∂Γ ∖ {c^+, c^-}` has a connected component with more than one point. Then the Schreier graph of `Γ` on
`Γ/⟨c⟩` is not quasi-isometric to a tree. This holds for every infinite-order `c` when `Γ` is one-ended.

**Theorem.** Let `Γ` be a one-ended hyperbolic group, e.g. a closed surface group, with `Γ ≤ V` acting on
`C = {0,1}^ℕ`.
1. Every point of `C` has a neighborhood fixed pointwise by some nontrivial element of `Γ`. Equivalently, by
   compactness, `C` is a finite disjoint union of clopen sets, each fixed pointwise by a nontrivial element.
2. If `Γ` is torsion-free, no element `w ∈ Γ` acts on `C` with north–south dynamics. This means there are no
   points `a ≠ r` such that `w^n(C ∖ N_r) ⊆ N_a` for all large `n`, for all neighborhoods `N_a` of `a` and
   `N_r` of `r`. Also, no two nontrivial elements of `Γ` have disjoint supports.

**For BBMZ survey Question 4.7** (`closed-hyperbolic-surface-groups-embed-in-thompson-v`). A negative answer now
needs only a *compression*: some `γ ∈ Γ` and some nontrivial `g ∈ Γ` with `γ(cl supp g)` inside a clopen set
fixed pointwise by a nontrivial element. Item 2 carries this out whenever `Γ` contains a north–south element. The
general case is open: elements of `V` can have several attractors and repellers, and a region where they act
periodically.
