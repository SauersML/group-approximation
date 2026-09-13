---
rg: 2
id: kohler-uct-for-zp-equivariant-bootstrap
kind: claim
title: Köhler's invariant of any Z/p-algebra is exact and realized in the equivariant bootstrap class, and maps from bootstrap objects lift module maps
distinct_from:
  bootstrap-zp-actions-realize-every-cyclotomic-k-module: that specializes this UCT to contractible restriction; this is the general theorem as imported.
---

**ESTABLISHED (literature import).** Let `p` be prime.
- `K_p` is Köhler's Z/2-graded ring. Its three vertices are the generators
  `C_p`, `C` and `C(Z/p)`, where `C_p` is the mapping cone of `C → C(Z/p)`.
- `U = U^(Z/p)` is his stable homological functor `KK^(Z/p) → K_p`-modules,
  with `U(A) = KK^(Z/p)_*(C_p ⊕ C ⊕ C(Z/p), A)`.

1. For a countable Z/2-graded `K_p`-module `M`, these are equivalent:
   - `M = U(A)` for some `A` in `B^(Z/p)`;
   - `M = U(A)` for some `A` in `KK^(Z/p)`;
   - `M` is exact;
   - `M` has a projective resolution of length 1.
2. Let `A` and `C` be separable `Z/p`-C\*-algebras with `A ∈ B^(Z/p)`. There
   is a natural short exact sequence
   `Ext^1_(K_p)(U(ΣA), U(C)) ↣ KK^(Z/p)(A, C) ↠ Hom_(K_p)(U(A), U(C))`.
   If `A, C ∈ B^(Z/p)`, every isomorphism `U(A) ≅ U(C)` lifts to a
   KK^(Z/p)-equivalence.

Citation: `kohler-uct-for-zp-equivariant-bootstrap-citation`.
