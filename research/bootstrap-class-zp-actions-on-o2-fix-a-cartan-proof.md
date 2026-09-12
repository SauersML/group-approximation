---
rg: 2
id: bootstrap-class-zp-actions-on-o2-fix-a-cartan-proof
kind: route
title: Descend the equivariant KK-equivalence to the crossed product and apply the one-action Cartan criterion
target: bootstrap-class-zp-actions-on-o2-fix-a-cartan
requires: [barlak-li-p-half-iff-zp-actions-fix-cartan, uct-class-permanence-properties]
artifacts:
  - research/artifacts/stw-uct-per-prime-cartan-2026-09-12.md
---

Let `(T, β)` be a `Z_q`-action on a separable type I C\*-algebra with
`(O_2, α) ≃ (T, β)` in `KK^(Z_q)`.

1. **Descent.**  Kasparov's descent `j_G : KK^G(A, B) → KK(A ⋊ G, B ⋊ G)` is
   compatible with the Kasparov product and sends identity classes to identity
   classes (Kasparov, Invent. Math. 91 (1988), Theorem 3.11).  So it sends a
   `KK^G`-equivalence to a KK-equivalence, and `O_2 ⋊_α Z_q ≃ T ⋊_β Z_q` in KK.
2. **Type I.**  For a finite group the regular covariant representation embeds
   `T ⋊_β Z_q` faithfully into `T ⊗ B(ℓ²(Z_q)) = M_q(T)`, which is type I.  A
   C\*-subalgebra of a type I C\*-algebra is type I (Dixmier, *C\*-algebras*,
   Proposition 4.3.5).  So `T ⋊_β Z_q` is separable and type I.
3. **UCT.**  Separable type I C\*-algebras satisfy the UCT (Rosenberg--Schochet,
   Duke Math. J. 55 (1987)).  By KK-invariance, item 1 of
   `uct-class-permanence-properties`, so does `O_2 ⋊_α Z_q`.
4. **Cartan.**  Part (a) of `barlak-li-p-half-iff-zp-actions-fix-cartan`
   (Barlak--Li II, Corollary 4.15) gives a Cartan subalgebra `C ⊆ O_2` with
   `α(C) = C`.
