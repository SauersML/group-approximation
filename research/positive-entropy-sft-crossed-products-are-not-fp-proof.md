---
rg: 2
id: positive-entropy-sft-crossed-products-are-not-fp-proof
kind: route
title: Entropy gives a doubly occurring ambiguous annulus, which is a wall certificate at every scale
target: positive-entropy-sft-crossed-products-are-not-fp
requires: [sft-crossed-product-fp-iff-quantum-rigid]
artifacts:
  - research/artifacts/sft-crossed-product-presentation-rigidity-2026-09-13.md
---

The artifact gives the proofs: Theorem 2 in Section 3 and Corollary 3 in Section 4.

1. **Wall certificate.** Let `T_1, T_2 ∈ Ω` agree on `M`, where `Z^2 = I ⊔ M ⊔ O` and
   `d(I, O) > 2D`, and let them differ somewhere in `I` and somewhere in `O`. Put `W = k^2`.
   - `E_a(z)` is `diag([T_1(z)=a], [T_2(z)=a])` in the basis `(w_1, w_2)` on `I ∪ M`, and in
     `(w_1 + w_2, w_2)` on `O`. On `M` the entries agree, so both descriptions coincide.
   - Balls of diameter `2D` never meet both `I` and `O`, so (Q1)–(Q3) hold.
   - The two rank-one idempotents at the difference points share their kernel and have different
     images, so they do not commute.
2. **Walls from entropy.** Fix `D` and put `w = max(2D, 2r) + 1`.
   - Choose an ergodic measure `mu` of positive entropy and put `X = supp mu`.
   - `exp(c n^2)` patterns on `B_(n+w)`, against `|A|^(O(wn))` patterns on the annulus
     `B_(n+w) \ B_n`, give an annulus pattern `p ∈ L(X)` with two fillings `f != f'`.
   - `mu([p]) > 0`, and recurrence gives `x ∈ X` containing `p` around `B_n` and around `B_n + g`,
     with `|g|` large.
   - Writing `f` in both boxes, respectively `f'` in both, gives configurations in `Ω`: every
     `r`-ball touching a box reads an occurring pattern.
   - They agree on the annulus and differ in `B_n` and in `B_n + g`.
3. **Conclusion.** `Ω` is not `D`-rigid for any `D`, so by `sft-crossed-product-fp-iff-quantum-rigid`
   the algebra is not finitely presented.
