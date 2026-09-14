---
rg: 2
id: topological-full-group-images-in-el3-are-not-confined
kind: claim
title: The images of [[T]] and [[T]]' inside EL_3(LC(X,F_2)⋊Z) are not confined
distinct_from:
  full-group-confined-subgroups-are-finite-set-stabilizers: that classifies confined subgroups inside the full group itself; this shows the full group, embedded in the Kazhdan group EL_3, is not confined there
---

**ESTABLISHED (unreviewed).**

Let `(X,T)` be an infinite Cantor minimal system, `R = LC(X,F_2) ⋊_T Z` and `G = EL_3(R)`.
- Let `H ≤ G` consist of matrices `diag(a, b, 1)` with `a, b ∈ R^×`.
- Suppose the first-coordinate map `diag(a,b,1) ↦ a` is injective on `H`.
Then `H`, and every subgroup of `H`, is not confined in `G`.

**Instances** (`topological-full-group-embeds-in-subshift-elementary-group`):
- the image of `[[T]]'` under `g ↦ diag(w_g, 1, 1)`;
- the image of `[[T]]` under `g ↦ diag(w_g, u^{−I(g)}, 1)`.

Here `w_g = Σ_n u^n e_{n_g = n}`, and `g ↦ w_g` is injective.

**Consequence.** The amenable simple group `[[T]]'` of the same system is not an obstruction to C*-simplicity of `G_X`
(`cstar-simple-iff-amenable-subgroups-not-confined`).

**Proof:** `topological-full-group-images-el3-not-confined-proof`.

**Review (sk-verify-13, 2026-09-13, `research/artifacts/sk-verify-13-2026-09-13-part1.md` §3):** PASS for the general statement. Re-derived `k_N p k_N^{-1} = p + u^N(a−1)E_31`, the diagonal and `(3,1)` comparisons, and Lemma B. The Instances are conditional on `topological-full-group-embeds-in-subshift-elementary-group`, which is unreviewed (queued with sk-referee-2).
