---
rg: 2
id: sl2-casimir-cannot-separate-verma-from-finite-dimensional-proof
kind: route
title: Compute the Casimir scalar on a highest-weight vector, and use the singular vector f^(k+1) v_k
target: sl2-casimir-cannot-separate-verma-from-finite-dimensional
requires: []
artifacts:
  - research/artifacts/gq-gq-k2-q-sl2-verma.md
---

Direct proof. This is standard `sl_2` representation theory (Bernstein–Gelfand–Gelfand; Humphreys,
*Representations of Semisimple Lie Algebras in the BGG Category O*, §1), and no novelty is claimed. Notation
as in the target.

1. **Scalar.** On the highest-weight vector, `e v_λ = 0` and `h v_λ = λ v_λ`. So
   `Ω v_λ = (2fe + h + ½h²) v_λ = (λ + ½λ²) v_λ = χ(λ) v_λ`. Since `Ω` is central and `v_λ` generates `M(λ)`,
   `Ω` acts on `M(λ)` by `χ(λ)`.
2. **Degeneracy.** `χ(-k-2) = ½(-k-2)(-k) = χ(k)`. From `e f^j v_λ = j(λ - j + 1) f^(j-1) v_λ` with
   `j = k+1` and `λ = k`, the vector `f^(k+1) v_k` is killed by `e`, and it has weight `k - 2(k+1) = -k-2`.
   `M(k)` is free over `Q[f]`, so the induced map `M(-k-2) -> M(k)` is injective. Its cokernel has basis
   `v_k, ..., f^k v_k` and is `L(k)`.
3. **No central separation.** `Z(U) = Q[Ω]` (Harish-Chandra, for `sl_2`). So `z = p(Ω)` acts on `M(k)` and on
   the submodule `M(-k-2)` by the same scalar `p(χ(k)) = p(χ(-k-2))`. A resolvent `(z - c)^(-1)` exists on
   `M(k)` exactly when `p(χ(k)) ≠ c`, and it then acts on all of `M(k)`, submodule included, by
   `(p(χ(k)) - c)^(-1)`.
