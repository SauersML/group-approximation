---
rg: 2
id: bk-radical-projection-quotients-are-toeplitz-infinite-proof
kind: route
title: Glue compact-free quotients of the radical with the spectral extension theorem, and pull corner traces of projection-generated quotients back to the radical
target: bk-radical-projection-quotients-are-toeplitz-infinite
requires:
  - bk-no-compact-open-ideals-are-qd-invisible
  - stw07-separating-qd-quotients-force-quasidiagonality
  - bk-radical-traces-vanishing-on-boundary-are-zero
  - moutzouris-singular-subgroup-has-vanishing-trace
  - brown-dadarlat-ext-trivial-class-gives-qd-extension
artifacts:
  - research/artifacts/bk-radical-trace-step-part4-2026-09-13.md
  - research/artifacts/bk-radical-trace-step-part3-2026-09-13.md
---

Proofs in Sections 1--3 of the part-4 artifact.

1. **Theorem 8.**  If `Prim(R/K)` were compact-free, the extension
   `0 -> R/K -> E/K -> E/R -> 0` (exact ideal, nuclear quasidiagonal quotient)
   would be quasidiagonal by `bk-no-compact-open-ideals-are-qd-invisible`.
   Minimality of the radical gives `R ⊆ K`.
2. **Theorem 9.**  If `R/K` is stably finite with `q_*(H)` singular, Lemma A
   (Moutzouris Proposition 2.6, Lemma 2.12, traces from states on exact
   algebras) gives a trace on a full corner annihilating `q_*(H)`.  Transport
   it along Brown's stable isomorphism and pull back along `q`.  The result is a
   nonzero densely finite trace on `R` annihilating `H`, which contradicts
   `bk-radical-traces-vanishing-on-boundary-are-zero`.  Spielberg's criterion
   (BD Proposition 4.1) gives infiniteness of `E/K`.
3. **Corollary 10.**  `Tr ∘ π_P` is densely finite for elementary closed points,
   since the Pedersen ideal of `K` is the finite-rank operators.  Gordan's
   alternative on the rank vectors gives the positive class.
4. **Corollary 11.**  Pull positive homomorphisms back to `K_0(R)` and apply
   Corollary 6.
