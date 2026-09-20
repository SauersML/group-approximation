---
rg: 2
id: relative-t-uniform-projection-from-cornulier-citation
kind: route
title: "Import Cornulier's Theorem 2.2.3 (uniform convergence of positive definite functions on the relative-(T) set), then use the lemma of the centre"
target: relative-t-subgroup-pairs-have-uniform-invariant-projection
requires: []
---

**Import.** Checked 2026-09-19 against Y. de Cornulier, *Relative Kazhdan property*, Ann. Sci.
ÉNS 39 (2006), arXiv:math/0505193, Section 2.

- Definition 2.1.1 (verbatim): "`(G, X)` has relative Property (T) if, for every net `(φ_i)` of
  continuous normalized positive definite functions that converges to 1 uniformly on compact
  subsets, the convergence is uniform on `X`."
- Theorem 2.2.3 lists, among others:
  - (3') "There exists `ε < √2` such that for every unitary representation `π` of `G` satisfying
    `1 ≺ π`, the representation `π` has a `(X, ε)`-invariant vector";
  - (4) "`(G, X)` has relative Property (FH)", i.e. every conditionally negative definite function
    is bounded on `X`.

  It proves (3') ⇒ (4), and: "Moreover, if `G` is σ-compact, then (4) ⇒ (1), so that they are all
  equivalent."
- Remark 2.2.4 says that for `X = H` a subgroup this recovers Jolissaint (Enseign. Math. 51 (2005)
  31–45).

Only these implications are imported, for a countable discrete group. Such a group is σ-compact, and
its compact subsets are its finite subsets.

**Step 1 (hypothesis gives (1)).** A nonzero `H`-invariant vector is `(H, ε)`-invariant for every
`ε`. So the hypothesis gives (3'), hence (4), hence (1) since `Γ` is countable. For a subset `X`,
the hypothesis is (4) itself, and again gives (1).

**Step 2 (uniform bound on `X`).** Fix `δ > 0` and suppose no finite `Q` and `ε > 0` work for the
first bullet.
- Index by pairs `j = (Q, k)`, with `Q ⊂ Γ` finite and `k ≥ 1`. Order them by `Q ⊆ Q'` and `k ≤ k'`.
  This is a directed set.
- For each `j` choose `(π_j, ξ_j)` with `ξ_j` a unit vector, `max_{g∈Q} ‖π_j(g)ξ_j − ξ_j‖ ≤ 1/k`,
  and `sup_{x∈X} ‖π_j(x)ξ_j − ξ_j‖ ≥ δ`.
- Put `φ_j(g) = ⟨π_j(g)ξ_j, ξ_j⟩`, a normalized positive definite function. By Cauchy–Schwarz,
  `|1 − φ_j(g)| ≤ ‖π_j(g)ξ_j − ξ_j‖ ≤ 1/k` for `g ∈ Q`. So `φ_j → 1` uniformly on finite sets.
- By (1), `s_j = sup_{x∈X} |1 − φ_j(x)| → 0`. Take `j` with `s_j < δ²/2`. Then
  `‖π_j(x)ξ_j − ξ_j‖² = 2 − 2 Re φ_j(x) ≤ 2 s_j` for every `x ∈ X`. So the supremum is at most
  `√(2 s_j) < δ`, a contradiction.

**Step 3 (projection, for `X = H` a subgroup).** Take `Q, ε` from Step 2 for this `δ`, and a unit
`ξ` that is `(Q, ε)`-invariant. Put `δ' = sup_{h∈H} ‖π(h)ξ − ξ‖`, so `δ' < δ`.
- Let `C` be the closed convex hull of `π(H)ξ`. For a finite convex combination,
  `‖Σ λ_i π(h_i)ξ − ξ‖ ≤ Σ λ_i ‖π(h_i)ξ − ξ‖ ≤ δ'`. This passes to the closure, so every point of
  `C` is within `δ'` of `ξ`.
- `C` is closed, convex, nonempty and `π(H)`-invariant, because `π(h)` is a linear isometry that
  permutes `π(H)ξ`. A closed convex subset of a Hilbert space has a unique element `c` of minimal
  norm. Each `π(h)c` lies in `C` and has the same norm, so `π(h)c = c`. Thus `c ∈ V^H`.
- `Pξ` is the point of `V^H` nearest to `ξ`, so `‖ξ − Pξ‖ ≤ ‖ξ − c‖ ≤ δ' < δ`. □

**Scope.** Countability of `Γ` is used only for (4) ⇒ (1). By Cornulier's Remark 2.2.5, for a group
that is not σ-compact, (3') ⇒ (1) is known only for normal `X`. This is why the target is stated
for countable `Γ`.
