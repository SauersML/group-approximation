---
rg: 2
id: rational-eigenvalue-iff-subshift-ring-is-matrix-ring-proof
kind: route
title: Cyclic clopen partitions give matrix units; matrix units give p-divisibility of [1] in K_0; reducing a coboundary mod p gives an eigenfunction
target: rational-eigenvalue-iff-subshift-ring-is-matrix-ring
requires:
  - subshift-crossed-product-k0-is-coinvariant-group
artifacts:
  - research/artifacts/sk-open-4-dictionary-2026-09-13-part2.md
---

Write `λ = e^(2πi/p)`, `σ(f) = f∘T^(−1)`, `u f u^(−1) = σ(f)`.

- **(1)⇒(2).**
  - For an eigenfunction `f`, `|f|` and `f^p` are invariant, so they are constant. So `f` takes the values `ζλ^a`.
  - `U = f^(−1)(ζ)` is clopen, and `f∘T = λf` gives `T^aU = f^(−1)(ζλ^a)`.
- **(2)⇒(1).** Put `f = λ^a` on `T^aU`.
- **(2)⇒(5).**
  - Put `E_ab = χ_(T^aU) u^(a−b)` for `0 ≤ a,b < p`. Then `E_ab E_cd = χ_(T^aU ∩ T^(a−b+c)U) u^(a−b+c−d)`. This is `δ_bc E_ad`, since the levels are disjoint and `|b−c| < p`. Also `Σ_a E_aa = 1`.
  - So `R_X ≅ M_p(E_00 R_X E_00)`.
  - Since `χ_U u^j χ_U = χ_(U ∩ T^jU) u^j` vanishes unless `p | j`, the corner is `LC(U,F_q) ⋊_(T^p) Z`.
  - Minimality of `T^p` on `U`: if `C ⊆ U` is closed and `T^p`-invariant, then `⊔_(i<p) T^iC` is closed and `T`-invariant, so it is `X`. Disjointness of the levels forces `C = U`.
- **(4)⇔(5).** Standard: a full set of matrix units `e_ab` gives `R ≅ M_p(e_11 R e_11)`, and conversely `M_p(F_q) ⊆ M_p(S)`.
- **(5)⇒(3).**
  - Matrix units give orthogonal, pairwise equivalent idempotents with sum 1, so `[1] = p[e_11]` in `K_0(R_X)`.
  - The required isomorphism `K_0(R_X) ≅ C(X,Z)/(1−T_*)C(X,Z)` sends `[1]` to `[χ_X]`.
- **(3)⇒(1).**
  - Write `χ_X = p h + g − g∘T^(−1)` with `h, g ∈ C(X,Z)`.
  - Reducing mod `p` gives `ḡ(Tx) − ḡ(x) = 1` in `Z/p`, so `f = λ^ḡ` is a continuous eigenfunction.
- **Groups.**
  - For `n ≥ 2`, `EL_n(M_p(S)) = EL_(np)(S)` inside `GL_(np)(S)`.
    - A block elementary matrix `I + rE_ij` (`i ≠ j`, `r ∈ M_p(S)`) is the product of the elementary matrices `e_((i,a),(j,b))(r_ab)`, which sit at distinct off-diagonal positions and commute.
    - Conversely, an elementary matrix `e_((i,a),(i,b))(s)` with `a ≠ b` inside one block is `[e_((i,a),(j,c))(s), e_((j,c),(i,b))(1)]` for any `j ≠ i`.
  - The cyclic partition is a factor map `X → Z/p`. Pulling back gives a unital equivariant injection `LC(Z/p,F_q) → LC(X,F_q)`, which extends to `R_(Z/p) ↪ R_X`.
  - The matrix-unit construction for `Z/p` itself gives `R_(Z/p) ≅ M_p(F_q[u^(±p)])`.
  - `F_q[t^(±1)]` is Euclidean, so `EL_m = SL_m` over it for `m ≥ 2`.
- **Factors.** `h ↦ h∘π` is injective, because `π` is onto; it is unital and equivariant, so it extends to crossed products. ∎

**Model tests.**
- Sturmian `X_α`: no rational eigenvalue, and `1 ∉ p(Z+αZ)` ✓.
- Toeplitz subshift with skeleton periods `p^k`: eigenvalues `e^(2πi/p^k)` and `[1]/p^k ∈ Z[1/p] ⊆ K^0` ✓.
- Periodic orbit of length `p` (not infinite): `R ≅ M_p(F_q[t^(±1)])` ✓.
