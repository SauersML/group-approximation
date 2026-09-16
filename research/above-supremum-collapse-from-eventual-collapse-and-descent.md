---
rg: 2
id: above-supremum-collapse-from-eventual-collapse-and-descent
kind: route
title: Eventual total collapse plus non-rigidity of every level above the supremum gives collapse at every level above it
target: bernoulli-shifts-above-rokhlin-supremum-are-isomorphic
requires:
  - bernoulli-collapse-is-null-or-eventually-total
  - eventual-bernoulli-collapse-at-finite-rokhlin-supremum
  - bernoulli-rigidity-threshold-equals-rokhlin-supremum
  - bernoulli-shifts-with-equal-base-entropy-are-isomorphic
---

Let `G` be countably infinite with `s = h^Rok_sup(G) < ∞`. "Item n" refers to the first prerequisite.

1. The second prerequisite gives `M < ∞` with all `X_h`, `h ≥ M`, isomorphic. By item 2, `D(G) = R`.
2. The third prerequisite says that every level `a > s` is non-rigid, so `r(G) = s`.
3. Item 4, implication (T2) ⇒ (T1), gives `X_h ≅ X_(h')` for all `s < h < h' < ∞`.
4. Let `(L, λ)` and `(K, κ)` be bases with `s < H(λ) < H(κ) < ∞`. By the fourth prerequisite,
   `L^G ≅ X_(H(λ)) ≅ X_(H(κ)) ≅ K^G`.

**The split is lossless.** By item 4, (T1) ⇒ (T2), the target implies both the second and the third prerequisite.
Neither of them follows from the other by the product calculus: the artifact of the first prerequisite, Section 5,
gives two formal models separating them.
