---
rg: 2
id: matricial-divisibility-kills-rational-k2-symbols-proof
kind: route
title: The unital map from Q factors through a diagonal embedding, which multiplies K_2 by n, and K_2(Q) is torsion
target: matricial-divisibility-kills-rational-k2-symbols
requires: []
---

**Inputs (textbook; trust surface).**
- **(T) Tate.** `K_2(Q) ≅ (Z/4)^x ⊕ ⊕_(p odd) (Z/p)^x`. This is Milnor, *Introduction to
  Algebraic K-theory*, §11, as quoted on the Wikipedia page "Algebraic K-theory" (fetched
  2026-09-17). In particular `K_2(Q)` is a torsion group.
- **(D) Diagonal maps multiply by `n`.** For a unital ring `A`, let `δ: A -> M_n(A)`,
  `a ↦ a I_n`, and let `μ: K_*(A) ≅ K_*(M_n(A))` be the Morita isomorphism. Then
  `δ_* = n·μ`. The reason: `δ` is the orthogonal sum of the `n` corner embeddings, which are
  conjugate to each other; each induces `μ`; and `K_*` is additive on orthogonal sums of ring
  maps. Referee C re-derived this from Milnor, *Introduction to Algebraic K-theory*, Theorems 5.1
  and 5.10. The block map `St(M_n B) -> St(B)` is an isomorphism, because both are universal
  central extensions of `E(B)`. The `n` block copies of a `K_2` class coincide, because
  conjugation by a lift of a block swap fixes the central `K_2`. See
  `research/artifacts/gq-referee-c-matricial-divisibility-kills-rational-k2-symbols.md`. On `K_1`
  it is the elementary fact that a block-diagonal matrix has the sum of the classes of its blocks.

**Proof.** Let `z ∈ K_2(Q)`. By (T), `z` has finite order `t`. Choose `n` with `t | n` and a
unital isomorphism `φ: M_n(R_n) -> R`.
- Integers are invertible in `M_n(R_n)`, hence in `R_n`. So `R_n` receives the unique unital
  map `j_n: Q -> R_n`.
- The composite `φ ∘ δ ∘ j_n: Q -> R` is a unital ring map. A unital map out of `Q` is unique,
  so this composite is the given map `ι: Q -> R`.
- On `K_2`, by (D):
  `ι_*(z) = φ_* δ_* (j_n)_*(z) = φ_* (n·μ((j_n)_*(z))) = φ_* μ((j_n)_*(n z)) = 0`,
  since `n z = 0`. ∎

For `K_1` the same computation gives `ι_*(λ) = φ_* μ((j_n)_*(λ^n))`. So the rational
scalars survive in `K_1(R)` exactly when their `n`-th powers survive in `K_1(R_n)`. That is
where the (K1) half has to be checked.
