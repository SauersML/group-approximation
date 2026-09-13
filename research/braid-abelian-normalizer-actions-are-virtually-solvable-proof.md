---
rg: 2
id: braid-abelian-normalizer-actions-are-virtually-solvable-proof
kind: route
title: The bi-order of the pure braid group restricts to an invariant order on the abelian subgroup
target: braid-abelian-normalizer-actions-are-virtually-solvable
requires: []
artifacts:
  - research/artifacts/zp-braid-haagerup-fences-2026-09-13-part2.md
---

1. **Magnus order.** The Magnus embedding `F_m → Z⟨⟨X_1, …, X_m⟩⟩`, `x_i ↦ 1 + X_i`, gives a bi-invariant order
   on `F_m`: `g > 1` iff the leading coefficient of the lowest-degree part of `μ(g) − 1` is positive.
2. **IA invariance.** An automorphism inducing the identity on `H_1(F_m)` sends `X_i ↦ X_i + (higher)` on the
   Magnus side, so it fixes lowest-degree parts and preserves the order.
3. **`P_n` is bi-orderable.** Pure braid automorphisms send each generator to a conjugate of itself, so they
   are IA. Order `P_n = F_{n−1} ⋊ P_{n−1}` lexicographically by induction (Kim–Rolfsen, Canad. J. Math. 55
   (2003)).
4. **Orders on `Z^k`.** If `Λ` acts on `Z^k` preserving a group order, it fixes each convex subgroup `C_i` of
   the finite chain of pure convex subgroups. On `C_i/C_{i−1}` the order is archimedean, with an order-embedding
   `ι` into `R` unique up to a positive scalar (Hölder), so each element acts as `ι ∘ γ = λ_γ ι`. The rational
   matrices with this property form a Q-algebra embedding into `R` via `M ↦ λ_M` (injective since `ι` is
   injective), hence a commutative one. So `Λ` acts abelianly on graded pieces and unipotently on the flag, and
   its image is solvable.
5. **Conclusion.** `Γ_0 = Γ ∩ P_n` normalizes `A_0 = A ∩ P_n`. Both have finite index, and the restricted bi-order
   on `A_0` is `Γ_0`-invariant. By step 4 the image of `Γ_0` in `GL(A_0)`, equivalently in `GL(A)`, is solvable,
   and it has finite index in the image of `Γ`.

Full text: §2 of `research/artifacts/zp-braid-haagerup-fences-2026-09-13-part2.md`.
