---
rg: 2
id: kk-tensor-power-norm-functor-to-kk-zp
kind: claim
title: The p-fold tensor power with the cyclic shift extends to a non-additive functor N from KK to KK^(Z/p)
distinct_from:
  zp-restriction-trivial-splits-cellular-plus-phantom: that splits objects with contractible restriction by the action element; this constructs a multiplicative induction functor producing Z/p-algebras from ordinary KK-classes.
---

**OPEN (lane ex2-uct-norm-functor, 2026-09-13).**  Let `p` be prime,
`G = Z/p`, and `KK` the Kasparov category of separable C\*-algebras with
`KK_0` morphisms.  For a separable `A` put `N(A) = A^(⊗p)` (minimal tensor
product) with the cyclic shift `σ`.  Is there a map of sets
`N : KK_0(A, B) → KK_0^G(N(A), N(B))` such that:

1. `N([f]) = [f^(⊗p)]` for every \*-homomorphism `f : A → B`;
2. `N(y ∘ x) = N(y) ∘ N(x)` and `N(1_A) = 1_(N(A))`;
3. `N(x ⊗ x') = N(x) ⊗ N(x')` for external products;
4. `N(x + y) = N(x) + N(y) + Σ_(orbits) Ind_1^G(w)`, the sum over the
   `(2^p − 2)/p` free orbits of mixed words, each `w` an external product of
   copies of `x` and `y`?

Consequences, if it holds (all proved in this lane from 1–2 alone):

* `N` sends KK-equivalences to KK^G-equivalences.
* `N(A) ≃_(KK^G) 0` whenever `A ≃_KK 0`, since
  `1_(N(A)) = N(1_A) = N(0) = 0`.  With
  `outer-actions-on-o2-kk-g-contractible-iff-rokhlin`, item 2, the shift on
  `O_2^(⊗p) ≅ O_2` is pointwise outer and contractible, so it has the Rokhlin
  property.
* `N(B) ⊆ B^G`: a bootstrap `A` is KK-equivalent to some `C_0(X)`, and
  `N(C_0(X)) = C_0(X^p)` with the permutation action is commutative.
* After tensoring with a Tate object `1_T` (cone of a cellular approximation
  `P → C` by induced objects, so `Res 1_T ≃ 0`), the induced terms in item 4
  die, and `Φ_T = 1_T ⊗ N(−)` is additive on morphisms.

**Model test.**  On `KK_0(C, C) = Z`, item 4 forces
`N(n) = n + ((n^p − n)/p)·ρ ∈ R(Z/p)`: the constant words are fixed, the
others fall into free orbits.  For `p = 2`, `N(n) = (n(n+1)/2)·1 + (n(n−1)/2)·χ`,
so `N(−1) = χ` (the odd line, graded flip) and `N(2) = 3 + χ`
(`Sym^2 ⊕ Λ^2` of `C^2`).  Multiplicativity checks: `N(−1)^2 = χ^2 = 1 = N(1)`
and `N(2)^2 = (3 + χ)^2 = 10 + 6χ = N(4)`.  This is Atiyah's power operation.

## Attempts

* **Cycle-level construction (in progress).**  For an even Kasparov cycle
  `(E, φ, F)` take `E^(⊗p)` over `B^(⊗p)` with the Koszul-signed shift, which
  is an honest action of `S_p`, and the operator `Σ_i M_i^(1/2) F_i`, where
  `F_i` is `F` in slot `i` and `(M_i)` is a Kasparov partition of unity.  The
  technical-theorem conditions on `(M_i)` are affine in the `M_i` and are
  permuted by the shift, so averaging a non-equivariant partition gives one
  with `σ(M_i) = M_(i+1)`.  Well-definedness needs: homotopies (restrict
  `C([0,1]^p)` to the diagonal), and degenerate cycles, where
  `p^(−1/2) Σ_i F_i` already squares to `1` and commutes with `φ^(⊗p)`.  Where
  it could die: item 2 needs a positivity-and-connection characterization of
  the equivariant product applied to shift-averaged operators.  Positivity
  mod compacts is convex, but the cycle condition `F^2 − 1 ∈ K` is not, so
  the averaging has to be done on the partitions, not on the operators.
* **Direct Cuntz trick for `N(O_2) ≃ 0` (dies).**  Recorded in the Attempts
  of `zp-restriction-and-crossed-product-detect-kk-g-contractibility`:
  `Σ_w Ad(S_w)` is an endomorphism of `N(O_2)`, not the identity.
