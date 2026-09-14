---
rg: 2
id: frobenius-bicommutants-make-subshift-el3-isos-standard
kind: claim
title: Given the index kernel theorem, the double centralizer of the image of a constant Frobenius group is one natural block, which forces orthogonality of supports, no fixed vectors, constant orientation, and so standardness of every isomorphism G_X → G_Y
distinct_from:
  singer-identities-make-subshift-el3-isos-standard: that assumes the Singer identities and (O′); this proves them from bicommutants and the index kernel theorem
  frobenius-support-idempotents-give-boolean-realization: that assumes (O) and (O′); this proves both
  subshift-el3-isomorphisms-are-standard-over-f2: that is the open question; this answers it modulo the unreviewed index kernel theorem
artifacts:
  - research/artifacts/sk-orthogonality-o-2026-09-14-part2.md
  - research/artifacts/sk-orthogonality-o-2026-09-14-part1.md
---

Let `X, Y` be infinite minimal subshifts, `G_X = EL_3(LC(X,F_2)⋊Z)`, `α: G_X → G_Y` an isomorphism, `Q = GL_3(F_2)`,
`F21 ≤ Q` the Frobenius group of order 21, `K_V = α(F21_V)` and `S_V = I + Σ_{k∈K_V} k`. Assume the index kernel
theorem `subshift-gl3-index-kernel-is-elementary-group` for `X` and `Y`. Then:

1. **(Lemma X)** `C_{G_X}C_{G_X}(F21_V) = Q_V`.
2. **(Theorem C)** On `R_Y³`, `K_V` has exactly one of the types `3`, `3*` and no type `2`. `α(Q_V)` is trivial on
   `Fix(K_V)` and acts as `ψ_V(q) ⊗ id` on the other block.
3. `S_VS_W = 0` for disjoint `V, W`, and `S_X = I`.
4. The orientation `t_V` does not depend on `V`.
5. **(Theorem D)** `α`, or `α∘γ_X` with `γ_X` the graph automorphism, satisfies the Singer identities. So `α` is
   standard, and `G_X ≅ G_Y` implies that `X` and `Y` are strongly orbit equivalent.

Status: proved in `frobenius-bicommutants-make-subshift-el3-isos-standard-proof`, unreviewed. It is conditional on
the unreviewed index kernel theorem and on the flagged first-return corner isomorphism.

Model tests:
- the identity, `inn(diag(u,1,1))` and `γ_X` all fit the conclusions;
- Petechuk's non-standard automorphism over a product ring breaks Lemma X, because the ring is not simple.
