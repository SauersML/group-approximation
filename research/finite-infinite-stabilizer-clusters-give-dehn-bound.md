---
rg: 2
id: finite-infinite-stabilizer-clusters-give-dehn-bound
kind: claim
title: "If the cells with infinite stabilizer form finite clusters, the Dehn action bound of Zaremsky Problem 1.17 holds with no hypothesis on face stabilizers"
distinct_from:
  llosa-isenrich-weis-dehn-bound-for-cocompact-actions: that assumes [G_e : G_σ] < ∞ for every face; this allows infinite-index faces and assumes instead that the infinite-stabilizer subcomplex has finite components, and it is proved by reducing to that theorem.
  dehn-bound-from-action-data-without-finite-index-faces: that asserts (UB) for every action in setting (S); this proves it for the class of actions whose infinite-stabilizer subcomplex has only finite components.
  some-action-violates-dehn-bound-without-finite-index-faces: that asks for a counterexample to (UB); this shows that no counterexample has finite infinite-stabilizer clusters.
---

**Statement.** Let `G` act on `X` as in setting (S) of
`zaremsky-1-17-dehn-function-from-cocompact-action-data`. Let `X_∞` be the
union of the closed cells with infinite stabilizer, and assume that every
connected component of `X_∞` is finite. Under normalization (N) of
`sol-lattice-actions-satisfy-the-dehn-action-bound`, there is `K ≥ 1` with

```text
δ_G(n) ≼ δ_X(n) · max_{x ∈ X^(0)} δ_{G_x}( K · δ_X(n) ).            (A)
```

Consequently:

- (UB), `δ_G(n) ≼ δ_X(n) · max_v δ_{G_v}( dist_X‾( δ_X(n) ) )`, holds for
  every finite generating set of `G` when each `δ_{G_x}` with `G_x` infinite
  satisfies `δ_{G_x}(Km) ≤ C δ_{G_x}(m)` (e.g. is `≃` to a polynomial).
- With no hypothesis on the `δ_{G_x}`, (UB) holds with `dist_X` computed from
  a suitable finite generating set of `G`.

**Commensurator criterion (Corollary B).** The components of `X_∞` are finite
if both:

- every edge `[u, v]` with infinite stabilizer has `[G_u : G_e]` and
  `[G_v : G_e]` finite;
- every infinite vertex stabilizer `H` has `[Comm_G(H) : H] < ∞`.

The proof is `finite-infinite-stabilizer-clusters-give-dehn-bound-proof`.
