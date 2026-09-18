---
rg: 2
id: kt-gamma-saturation-zero-one-law-proof
kind: route
title: In a wall the saturation is a compressor-stable kernel overgroup with polynomial roots, so the vertex-compressor sandwich makes it Gamma
target: kt-gamma-saturation-is-gamma-or-contains-e
requires:
  - kt-compressor-commutant-collapse-is-all-or-nothing
  - kt-compressor-stable-kernel-overgroups-are-polynomial
  - kt-hyperlinear-floor-is-root-invisible-laurent-overgroup
  - relative-embedding-is-commutant-separation
  - binary-free-and-ordinary-coset-wreaths-share-hyperlinearity
---

Notation as in the target. `SL_d(N) = SL_d(Z) ∩ M_d(N)` (= `Mon`), `β_L(x^m) = x^(Lm)`,
`L e_ij(f) L^(-1) = e_ij(β_L f)`. Write `S = Γ^sat(π)` and `ρ : G → SL_d(Z)` for the
projection. By Suslin (`r ≥ 3`), `Γ = EL_r(R_+) = SL_r(R_+)`.

## 1. `S` is a compressor-stable subgroup containing `Γ`

`S` is the preimage of the centralizer `C_U(C_0)`, so it is a subgroup. `π(Γ)` commutes with
`C_0 = C_U(π(Γ))`, so `Γ ≤ S`.

Let `t ∈ P_Γ`, i.e. `tΓt^(-1) ≤ Γ`, so `Γ ≤ t^(-1)Γt`. For `c ∈ C_0` the element
`c' = π(t)^(-1) c π(t)` commutes with `π(t^(-1)Γt) ⊇ π(Γ)`, so `c' ∈ C_0`. For `g ∈ S`,

```text
π(tgt^(-1)) c π(tgt^(-1))^(-1) = π(t) π(g) c' π(g)^(-1) π(t)^(-1) = π(t) c' π(t)^(-1) = c.
```

So `tSt^(-1) ≤ S`. Every `L ∈ SL_d(N)` is a compressor, since `LΓL^(-1) = EL_r(β_L R_+) ≤ Γ`.

## 2. The wall case: `S ∩ E = Γ`

Suppose `E ⊄ S`, i.e. some `π(e)`, `e ∈ E`, fails to commute with `C_0`. This is the failure
of condition 4 of `kt-compressor-commutant-collapse-is-all-or-nothing`, which holds for every
homomorphism into every group. Its wall alternative gives

```text
S ∩ U_kl(R) = U_kl(R_+)     for all k ≠ l.
```

Put `H = S ∩ E`. Then `SL_r(R_+) = Γ ≤ H ≤ E ≤ SL_r(R)`. `E` is normal in `G`, so by §1
`L·H = LHL^(-1) ≤ H` for every `L ∈ SL_d(N)`, where `L·` is `β_L` applied entrywise. And
`H ∩ U_12(R) = U_12(R_+)`. These are exactly the hypotheses of
`kt-compressor-stable-kernel-overgroups-are-polynomial` (proved by vertex-cone compressors in
`kt-kernel-overgroups-polynomial-via-vertex-compressors-proof`). Hence `H = SL_r(R_+) = Γ`.

## 3. The wall case: `ρ(S) = {I}`, so `S = Γ`

Keep `E ⊄ S`. `H = S ∩ E = Γ` is normal in `S`. Let `s = gL ∈ S` with `g ∈ E`,
`L = ρ(s) ∈ SL_d(Z)`. Then `sΓs^(-1) = Γ`, and `s e_ij(a) s^(-1) = g e_ij(β_L a) g^(-1)`.

**`L` is a permutation matrix.** Put `X_ij = gE_ijg^(-1) ∈ M_r(R)`. For `a ∈ R_+`,
`g e_ij(β_L a) g^(-1) = I + β_L(a) X_ij ∈ Γ ≤ M_r(R_+)`. With `a = 1` this gives `X_ij ∈ M_r(R_+)`
for `i ≠ j`. Fix `j`, choose `k ≠ j`; for `i ≠ j` we have `X_ij X_ji = gE_iig^(-1)`, and
`X_jk X_kj = gE_jjg^(-1)`. So

```text
β_L(a)·I = Σ_(i≠j) (β_L(a) X_ij) X_ji + (β_L(a) X_jk) X_kj ∈ M_r(R_+),
```

and `β_L(R_+) ⊆ R_+`. Since `β_L(x_c) = x^(Le_c)`, `L` has nonnegative entries. The same
argument for `s^(-1) = L^(-1)g^(-1) = (L^(-1)g^(-1)L)L^(-1) ∈ S` shows `L^(-1)` has
nonnegative entries. A nonnegative integer matrix with nonnegative integer inverse is a
permutation matrix. So `F = ρ(S)` lies in the finite group of permutation matrices of
determinant `1`.

**`F` is trivial.** Let `σ ∈ F` and `i ≠ j`. `T = I + E_ij ∈ SL_d(N)`, so by §1
`T^n S T^(-n) ≤ S` and `T^n σ T^(-n) ∈ F` for all `n ≥ 0`. `F` is finite, so
`T^a σ T^(-a) = T^b σ T^(-b)` for some `a < b`, and `T^k = I + kE_ij` (`k = b − a ≥ 1`)
commutes with `σ`. Now `σ(I + kE_ij)σ^(-1) = I + kE_(σ(i)σ(j))`, so `σ(i) = i` and `σ(j) = j`.
As `i ≠ j` are arbitrary, `σ = I`.

So `S ≤ E` and `S = S ∩ E = Γ`. This proves the theorem. ∎

## 4. Corollaries

**(1)** `G` is residually finite, hence hyperlinear, and by
`relative-embedding-is-commutant-separation` `K_Γ` is the intersection, over all canonical CE
actor models `σ` and all projections `p ∈ σ(Γ)' ∩ M`, of the commutation stabilizers of `p`.
A von Neumann algebra is the norm-closed span of its projections, so the stabilizers
intersected over the projections of one model give `Γ^sat(σ)`. Hence
`K_Γ = ∩_σ Γ^sat(σ)`. Each term is `Γ` or contains `E`, so `K_Γ = Γ` or `E ≤ K_Γ`. By part
(a) of `kt-hyperlinear-floor-is-root-invisible-laurent-overgroup`, `K_Γ ≤ E`. So
`K_Γ ∈ {Γ, E}`, and alternative 3 of its trichotomy (`Γ < K_Γ < E`) is empty.

**(2)** Given `Γ ≤ Δ` with `E ⊄ Δ` and `W_Δ` hyperlinear, `K_Γ ≤ Δ`
(`binary-free-and-ordinary-coset-wreaths-share-hyperlinearity`, leastness), so `K_Γ ≠ E` and
`K_Γ = Γ`, i.e. `W_Γ` is hyperlinear. The converse is `Δ = Γ`.

**(3)** If a canonical CE actor model `σ` has `u ∈ σ(Γ)' ∩ M` not commuting with
`σ(e_12(x_1^(-1)))`, then `e_12(x_1^(-1)) ∈ E ∖ Γ^sat(σ)`, so `Γ^sat(σ) = Γ` by the theorem.
For each of the countably many `g ∈ G ∖ Γ`, pick a projection `p_g ∈ σ(Γ)' ∩ M` that
`σ(g)` does not commute with (it exists because projections span). The common commutation
stabilizer of `{p_g}` contains `Γ` and misses every `g ∉ Γ`, so it is exactly `Γ`. By
`relative-embedding-is-commutant-separation`, `L(Γ) ≤ L(G)` is scalar relatively
embeddable, and `W_Γ` is hyperlinear. Conversely, if `W_Γ` is hyperlinear then `K_Γ = Γ`,
so some model has a `Γ`-central projection moved by `e_12(x_1^(-1))`.

**(4)** `W_Γ` is non-hyperlinear iff `K_Γ ≠ Γ`, iff `K_Γ = E` by (1), iff some single
`h ∈ E ∖ Γ` lies in `K_Γ`. If `K_Γ = E`, condition 4 of the all-or-nothing theorem holds in
every canonical CE actor model, hence condition 2 ((CCR) for every compressor). Conversely
(CCR) for one strict monomial compressor in every model gives condition 4 in every model, so
`E ≤ K_Γ`.

## 5. Calibration

* **Genuine finite-dimensional models** (`U = U(n)`, `π` a representation) satisfy
  condition 1 of the all-or-nothing theorem by dimension, so `E ≤ Γ^sat(π)`: no wall, which
  is consistent with the theorem and with residual finiteness of `G`.
* **Clifford-cover walls.** `kun-thom-clifford-cover-weakly-sofic` realizes a wall in a
  metric ultraproduct of finite groups. There the theorem says the bicommutant saturation of
  `Γ` is exactly `Γ`: the weakly sofic Clifford model separates every element of `G ∖ Γ` from
  `Γ` by the `Γ`-commutant, not only the Laurent roots.
* **Where `d ≥ 3` is used.** Only through the wall alternative of the all-or-nothing theorem
  (its subring dichotomy). §2's sandwich input holds for all `d ≥ 1`, and §3 for all `d ≥ 2`.
