---
rg: 2
id: subshift-group-unitary-embeddings-are-corner-subfactors
kind: claim
title: G_X is a subgroup of U(M) for a finite von Neumann algebra M iff a corner of M contains L(G_X) unitally, so each separable II_1 factor holds L(G_X) in corners for countably many X only
distinct_from:
  separable-factors-hold-countably-many-subshift-groups: that counts subshifts X with G_X in the unitary group of a separable factor; this identifies such embeddings with corner subfactor embeddings of L(G_X), so the count applies to subfactors.
  subshift-elementary-groups-are-character-rigid: that classifies characters of G_X; this reads the classification as a statement about every homomorphism of G_X into a finite von Neumann algebra.
artifacts:
  - research/artifacts/sk-vn-rigidity-2026-09-14.md
---

**ESTABLISHED (unreviewed, lane sk-vn-rigidity, 2026-09-14)** by route `subshift-group-unitary-embeddings-are-corner-subfactors-proof`.

Let `X` be an infinite minimal subshift, `G_X = EL_3(LC(X,F_2) ⋊_T Z)`, and `(M, τ)` a von Neumann algebra with a faithful
normal tracial state.
- **(1)** For every nontrivial homomorphism `ι: G_X → U(M)` there is a projection `z ∈ M`, `τ(z) = 1 − c > 0`, with
  `ι(g) = (1 − z) + ι(g)z` for all `g`, and `g ↦ ι(g)z` extends to a trace-scaled isomorphism `L(G_X) ≅ ι(G_X)''z ⊆ zMz`.
  Here `c = τ(ι(e_12(e_P)))` for any nonempty clopen `P`.
- **(2)** So `U(M)` contains a copy of `G_X` iff some nonzero corner `zMz` contains a unital copy of `L(G_X)`.
- **(3)** For a separable II_1 factor `M` and a finite alphabet `A`, only countably many infinite minimal subshifts `X ⊆ A^Z`
  have `L(G_X)` in a corner of `M`.

So up to a trivial summand, every homomorphism of `G_X` into a finite von Neumann algebra is the left regular
representation.

## Review
- **sk-verify-18 PASS (2026-09-14, `research/artifacts/sk-verify-18-2026-09-14-part8.md`):** re-derived: τ∘ι is a character, hence c·1 + (1−c)δ_e; the GNS space L²(N,τ) = π_0 ⊕ λ, disjoint; the central isotypic projection z; trace scaling τ(1−z) = c; the converse λ ⊕ 1; the corner count via the reviewed separable-factors node; all three model tests.
