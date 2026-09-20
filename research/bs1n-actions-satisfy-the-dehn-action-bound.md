---
rg: 2
id: bs1n-actions-satisfy-the-dehn-action-bound
kind: claim
title: "Every action of a solvable Baumslag–Solitar group BS(1,q) in the setting of Zaremsky Problem 1.17 satisfies the Dehn action bound (UB)"
distinct_from:
  sol-lattice-actions-satisfy-the-dehn-action-bound: that covers the groups Z^2 x_M Z with M hyperbolic, using an invariant area form; this covers BS(1,q) = Z[1/q] x Z, using the finite-cluster collapse.
  some-action-violates-dehn-bound-without-finite-index-faces: that asks for a counterexample to (UB) among all groups; this shows that no action of BS(1,q) is one.
  llosa-isenrich-weis-dehn-bound-for-cocompact-actions: that proves (UB) for complexes with finite-index face stabilizers; this covers arbitrary complexes in (S), including infinite-index faces, for the groups BS(1,q).
---

**Statement.** Let `q ≥ 2` and `G = BS(1, q) = ⟨a, t | t a t⁻¹ = a^q⟩`. Let
`G` act on `X` as in setting (S) of
`zaremsky-1-17-dehn-function-from-cocompact-action-data`. Under normalization
(N) of `sol-lattice-actions-satisfy-the-dehn-action-bound`, for every finite
generating set of `G`,

```text
δ_G(n) ≼ δ_X(n) · max_v δ_{G_v}( dist_X‾( δ_X(n) ) ).          (UB)
```

The proof is `bs1n-actions-satisfy-the-dehn-action-bound-proof`.
