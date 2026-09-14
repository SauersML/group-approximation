---
rg: 2
id: subshift-el-group-bi-interpretable-with-its-ring
kind: claim
title: For an infinite minimal subshift, EL_3(LC(X,F_2)⋊Z) and that ring are bi-interpretable with parameters, because bounded elementary generation makes the group an existentially definable subgroup of GL_3 of the ring
distinct_from:
  subshift-el-group-interprets-its-crossed-product-ring: that is one direction, the ring read off the group; this adds the converse and the two definable composites, and it is the statement that needs bounded elementary generation.
  subshift-el-groups-boundedly-elementary-generated: that is the bound itself, a statement about products of 78 elementary matrices; this is the model-theoretic consequence.
artifacts:
  - research/artifacts/sk-first-order-plan-2026-09-14.md
---

**Statement.** Let `X` be an infinite minimal subshift, `R = LC(X,F_2)⋊_T Z` and `G = EL_3(R)`. Then `G` and `R` are bi-interpretable with parameters.

**The two interpretations.**
- `R` in `G`: `subshift-el-group-interprets-its-crossed-product-ring`.
- `G` in `R`, with no parameters: by `subshift-el-groups-boundedly-elementary-generated`, with the positions `(i_k,j_k)` fixed,

      G = { M ∈ R^9 : ∃ r_1 … r_78, M = ê_{i_1j_1}(r_1) ⋯ ê_{i_78j_78}(r_78) },

  an existential formula in the ring.

**The composites.**
- On the ring side, `r ↦ e_13(r) ↦ r` has definable graph.
- On the group side, the map to the interpreted copy `G^*` is

      Θ(g,M) :⟺ ∃ a_1 … a_78 ∈ U_13 [ g = ∏_k w_{i_kj_k} a_k w_{i_kj_k}^{-1} ∧ M = ∏_k ê_{i_kj_k}(a_k) ].

  It is total by the bound, single-valued because both products name the same matrix, injective because `G` is a group of matrices, and surjective and multiplicative because the bound also applies to products.

**Why the bound is the point.** Without it, `EL_3(R)` is a union over `n` of sets of `n`-fold products, which is not first-order in `R`, and the tuple in `Θ` has no fixed length. This is exactly the obstacle recorded in `research/artifacts/sk-free-3-plan-2026-09-13.md` §5(iii).

**Consequences, to be developed separately.** `Th(G) ≡_T Th(R)`; hereditary undecidability of `Th(G)` once the classical undecidability of the theory of `F_q[t^{±1}]` is imported; and, if `R_X` turns out to be bi-interpretable with `(N,+,·,L(X))`, first-order rigidity of `G_X` for recursive `L(X)`.

**Scope.** Minimal Cantor system, coefficients `F_2`, rank 3. Nothing is claimed for `EL_2`, other coefficient rings, or the lamplighter hosts, where no bounded elementary generation is known.

**Status: established** by `subshift-el-group-bi-interpretable-with-its-ring-proof`, conditional on the bounded generation claim (reviewed twice, PASS-WITH-FIXES). UNREVIEWED; queued in the wave-12 verifier queue.

## Review
- **sk-verify-18 PASS (2026-09-14, `research/artifacts/sk-verify-18-2026-09-14-part10.md`):** re-derived (a) existential definability of G in R from Theorem D fixed positions; (b) the R-side composite r ↦ ê_13(r); (c) Θ total, single-valued, injective, onto G* and multiplicative. Conditional on Theorem D and its fixed pattern.
