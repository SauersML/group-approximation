---
rg: 2
id: leavitt-tensor-powers-have-vanishing-k-theory-in-all-degrees
kind: claim
title: Over every field, every tensor power of the Leavitt algebra L_k(1,2) has vanishing algebraic K-theory in every degree
distinct_from:
  leavitt-tensor-powers-have-trivial-k-theory: that asks only for K_1 = K_2 = 0 over F_2 with d >= 3; this is K_n = 0 for every n ∈ Z, every field and every d, and a route derives that claim from this one.
  prime-field-leavitt-tensor-powers-have-trivial-k-theory: that asks for K_1 = K_2 = 0 over each F_p with d >= 3; this is every degree over every field, and a route derives that claim from this one.
  ara-cortinas-leavitt-tensor-k-theory-vanishes: that imports d <= 2, through regular supercoherence of the second tensor factor; this handles every d, through the crossed product by Z^(d−1) and the Farrell–Jones conjecture.
  leavitt-crossed-product-coefficient-ring-is-k-trivial: that is vanishing for the coefficient ring C = L_0^(⊗(d−1)) ⊗ L; this is vanishing for the crossed product C ∗ Z^(d−1) = L^(⊗d) itself.
artifacts:
  - research/artifacts/leavitt-tensor-k-theory-farrell-jones-2026-09-12.md
---

**ESTABLISHED (derivation from imports).** Let `k` be a field, `L = L_k(1,2)`
and `d >= 1`. Then

```text
K_n(L^(⊗d)) = 0    for every n ∈ Z,
```

in non-connective algebraic `K`-theory. In particular `K_1 = K_2 = 0` for every
`d`, over `F_2` and over every `F_p`.

**Why it works although `L ⊗ L` is not coherent.**
- `L^(⊗d)` is a crossed product of the coefficient ring
  `C = L_0^(⊗(d−1)) ⊗ L` by `Λ ≅ Z^(d−1)`
  (`leavitt-tensor-powers-are-twisted-crossed-products`).
- The Farrell–Jones conjecture holds for `Z^(d−1)` with coefficients in additive
  categories, so it computes `K(C ∗ Λ)` from the crossed products `C ∗ H` over the
  virtually cyclic subgroups `H`.
- Each such `C ∗ H` is `C` itself or a skew Laurent ring `C_φ[t, t^−1]` over `C`.
- `C` is semihereditary with regular coherent Laurent extensions and `K(C) ≃ 0`
  (`leavitt-crossed-product-coefficient-ring-is-k-trivial`). Its twisted Nil
  terms vanish (Bartels–Lück), so every `C ∗ H` is `K`-trivial.
- The non-coherent intermediate rings of
  `leavitt-tensor-powers-are-not-left-coherent` never enter the computation.

Route: `leavitt-tensor-powers-k-vanishing-via-farrell-jones-proof`.

**Status and credit.**
- Derived 2026-09-12 by lane `bh-leavitt-nil-k-regularity`, on top of the
  crossed-product decomposition by lane `bh-coherence-kumjian-pask`.
- Not independently reviewed yet.
- No novelty is claimed: this is a standard use of the Farrell–Jones conjecture
  with coefficients. None of the sources read states it for Leavitt tensor
  powers with `d >= 3`.
