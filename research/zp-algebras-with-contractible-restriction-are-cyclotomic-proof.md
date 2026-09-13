---
rg: 2
id: zp-algebras-with-contractible-restriction-are-cyclotomic-proof
kind: route
title: The cone of 1 minus a character is a free circle, which kills any algebra with contractible restriction
target: zp-algebras-with-contractible-restriction-are-cyclotomic
requires: []
---

Let `L = C_χ` be the one-dimensional representation, `S^1 ⊂ L` the unit circle
with the free rotation action of `G`, and `B = C_0(L)`.

**Step 1: the cone of `1 − χ`.**  The pair `(closed unit disc, S^1)` gives the
semisplit equivariant extension `0 → C_0(open disc) → C(disc) → C(S^1) → 0`.
Here `C(disc) ≃_(KK^G) C` by the equivariant contraction to the origin, and
`C_0(open disc) = C_0(L)`.  Equivariant Bott periodicity for the complex
representation `L` identifies `C_0(L)` with `C` up to a double suspension.  The
composite `C_0(L) → C(disc) ≃ C` is then the Euler class of `L` in
`KK^G(C, C) = R(G)`, which is `1 − χ` up to a unit and sign convention.  So
`C(S^1)` with the rotation action is, up to suspension, the cone of
multiplication by `1 − χ` on `C`.

**Step 2: free circles kill `D`.**  Cover `S^1` by two open arcs `U, V`, each a
disjoint union of `p` translates of a short arc `I`.  Then
`C_0(U) ⊗ D ≅ Ind_1^G (C_0(I) ⊗ Res D)`, and similarly for `V` and `U ∩ V`
(the latter with two arcs per translate).  Induction–restriction adjunction
gives `KK^G(Ind_1^G X, E) = KK(X, Res E)`, so each induced term is
KK^G-contractible once `Res D ≃ 0`: take `E` to be the algebra itself.  The
Mayer--Vietoris extension
`0 → C_0(U ∩ V) ⊗ D → (C_0(U) ⊕ C_0(V)) ⊗ D → C(S^1) ⊗ D → 0` is semisplit
through a partition of unity.  So `C(S^1) ⊗ D ≃_(KK^G) 0`.

**Step 3: invertibility.**  Tensor Step 1 with `D`.  Multiplication by
`1 − χ` on `D` has a cone KK^G-equivalent, up to suspension, to
`C(S^1) ⊗ D ≃ 0`, so it is a KK^G-equivalence.  Hence `1 − χ` acts invertibly
on `S` and on every `KK^G(D, E)`, `KK^G(E, D)`.

**Step 4: arithmetic.**  `χ ρ = ρ` in `R(G)`, so `(1 − χ)ρ = 0`, and `ρ` acts as
zero.  The action of `R(G)` on `S` factors through
`R(G)/(ρ) ≅ Z[x]/(Φ_p) = Z[ζ_p]`.  There `p = ∏_(k=1)^(p−1) (1 − ζ^k)`, and
each factor divides the unit `1 − ζ`, as in
`order-p-automorphism-kk-cyclotomic-structure-proof` Step 5.  So `p` acts
invertibly.

**Model test.**  `D = C(G)` with translation has `Res D = C^p`, which is not
contractible.  Here `ρ` acts as `p`, not `0`, since `C(G) ⊗ L ≅ C(G)`
equivariantly.  The hypothesis is needed.

**Caveat on Step 1.**  The identification of the Euler class of `C_χ` with
`1 − χ` (rather than `1 − χ̄`) depends on conventions.  Either is a unit multiple
of the other in `Z[ζ_p]`, because `1 − ζ^(−1) = −ζ^(−1)(1 − ζ)`, so the
conclusions do not depend on it.
