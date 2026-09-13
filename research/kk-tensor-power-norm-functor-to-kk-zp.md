---
rg: 2
id: kk-tensor-power-norm-functor-to-kk-zp
kind: claim
title: The p-fold tensor power with the cyclic shift extends to a non-additive functor N from KK to KK^(Z/p)
distinct_from:
  zp-restriction-trivial-splits-cellular-plus-phantom: that splits objects with contractible restriction by the action element; this constructs a multiplicative induction functor producing Z/p-algebras from ordinary KK-classes.
---

**ESTABLISHED (derivation, lane ex2-uct-norm-functor, 2026-09-13; unreviewed;
standard inputs flagged in the artifacts).**  Let `p` be prime, `G = Z/p`, all
algebras separable, `⊗` minimal, and `N(A) = (A^(⊗p), σ)` with the cyclic
shift `σ`.

1. **Contractible norms.**  If `A ≃_KK 0`, then `N(A) ≃_(KK^G) 0`.
2. **Equivalences.**  If a \*-homomorphism `f : A → B` is a KK-equivalence,
   then `f^(⊗p)` is a `KK^G`-equivalence.
3. **The functor.**  There is a unique functor `N : KK → KK^G` with
   `N(A) = (A^(⊗p), σ)` and `N([f]) = [f^(⊗p)]` for \*-homomorphisms `f`.  It
   is not additive: on `KK(C, C) = Z` and `p = 2`, `N(2) = 3 + χ ∈ R(Z/2)`.
4. **Bootstrap norms.**  `N(B) ⊆ B^G`.
5. **Action element.**  `θ_(N(A)) = [σ]`.  It is `1` on `N(C)` and `N(M_n)`,
   and not `1` on `N(C ⊕ C)`, which has induced summands.

**How.**
- Item 1: tensor powers of Kasparov cycles, with a Kasparov partition of unity
  averaged over the shift.  Only the partition is averaged, never the
  operator.  This gives an exactly shift-invariant operator.  A homotopy from
  `id_A` to `0` then norms to an equivariant homotopy.
- Item 2: the mapping-cylinder filtration of `N(Z_f)`.  Its middle layers are
  induced from KK-contractible algebras, since `p` is prime.  Its top layer is
  `N(C_f)`, killed by item 1.
- Item 3: the localization universal property of `KK`.
- Item 4: Rosenberg--Schochet commutative models and the Meyer--Nadareishvili
  description of `B^G`.

**Model test.**  Atiyah's power operation is the case `KK(C, C) = Z`.  There
`N(n) = n + ((n^p − n)/p) ρ`, so for `p = 2`: `N(−1) = χ`, `N(2) = 3 + χ`, and
`N(2)^2 = 10 + 6χ = N(4)`.  The trivial functor `A ↦ (A, id)` fails item 5,
since `θ = 1` on every object.

**Not proved here.**  The cycle-level norm represents `N(x)` for every KK-class
`x`, the sum formula `N(x + y) = N(x) + N(y) + Σ_(free orbits) Ind(…)`, and
`N(x ⊗ x') = N(x) ⊗ N(x')` for general classes.  They hold for
\*-homomorphisms and direct sums of them.

**Uses.**
- `o2-tensor-power-shift-is-rokhlin`: the shift on `O_2^(⊗p)` is Rokhlin.
- The Tate part `1_T ⊗ N(A)` of the norm of a non-bootstrap algebra is a
  concrete test object for
  `zp-restriction-and-crossed-product-detect-kk-g-contractibility` (part 2,
  §8).

Proof: `kk-tensor-power-norm-functor-to-kk-zp-proof`.
