---
rg: 2
id: leavitt-tensor-powers-are-twisted-crossed-products
kind: claim
title: Every tensor power L_k(1,2)^(⊗d) with d >= 2 is a unital crossed product of L_0^(⊗(d-1)) ⊗ L by Z^(d-1)
distinct_from:
  leavitt-tensor-powers-are-not-left-coherent: that refutes coherence using the total-degree-zero Bernoulli subring of L ⊗ L; this decomposes the whole of L^(⊗d) as a crossed product over a coefficient ring that is coherent, so its K-theory can be computed without the non-coherent module categories.
  leavitt-tensor-powers-have-trivial-k-theory: that asserts K_1 = K_2 = 0 for d >= 3; this is a structural decomposition of the ring, and gives no K-group by itself.
artifacts:
  - research/artifacts/leavitt-tensor-crossed-product-2026-09-12.md
---

**ESTABLISHED (derivation).** Let `k` be a field, `L = L_k(1,2)` with its
`Z`-grading, and `d >= 2`. Let `Λ = {v ∈ Z^d : Σ_i v_i = 0} ≅ Z^(d−1)` and
`C = L_0^(⊗(d−1)) ⊗ L`.

Then `L^(⊗d)` is a crossed product `C ∗ Λ` in Passman's sense:

```text
L^(⊗d) = ⊕_(λ ∈ Λ) u^λ C,    u^λ ∈ (L^(⊗d))^x,    u^λ C (u^λ)^(−1) = C,
u^λ u^μ = ω(λ, μ) u^(λ+μ)  with  ω(λ, μ) ∈ C^x.
```

**The units.**
- In positions `j, j+1`, `u_j = Σ_i x_i ⊗ y_i` is a unit of degree
  `e_j − e_(j+1)`, with inverse `Σ_i y_i ⊗ x_i`.
- For `λ = Σ_j m_j (e_j − e_(j+1))`, `u^λ = u_1^(m_1) ⋯ u_(d−1)^(m_(d−1))`.

**The cocycle is not trivial.** For `d = 3`, `u_1 u_2 = Σ_i x_i ⊗ 1 ⊗ y_i`,
while `u_2 u_1 = Σ_(i,l) x_i ⊗ x_l y_i ⊗ y_l`.

**Sub-crossed products.** Each `C ∗ H` with `H ≤ Λ` infinite cyclic is a skew
Laurent ring `C[t, t^(−1); α]` by an automorphism. Two examples:
- `C ∗ Z(e_(d−1) − e_d) = L_0^(⊗(d−2)) ⊗ L ⊗ L`;
- `C ∗ Z(e_1 − e_2)` contains the Bernoulli crossed product of
  `leavitt-tensor-powers-are-not-left-coherent`.

The crossed product `L^(⊗d)` is not coherent
(`leavitt-tensor-powers-are-not-left-coherent`), while `C` is regular
supercoherent (`leavitt-crossed-product-coefficient-ring-is-k-trivial`).

**Use.** It reduces `leavitt-tensor-powers-have-trivial-k-theory` and its
prime-field twin to a Farrell–Jones statement for `Z^(d−1)` with coefficients
in `C`. There, `K(C) = 0` in every degree and `C` is uniformly regular. See
Section 4 of the artifact. That step is not established here.

Route: `leavitt-tensor-crossed-product-proof`.
