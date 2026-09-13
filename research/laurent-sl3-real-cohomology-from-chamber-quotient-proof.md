---
rg: 2
id: laurent-sl3-real-cohomology-from-chamber-quotient-proof
kind: route
title: Density puts one chamber in the quotient; Kazhdan stabilizers kill row one, properness kills rows three and up, and the spectral sequence degenerates
target: laurent-sl3-real-cohomology-from-chamber-quotient
requires:
  - elementary-groups-over-fg-rings-have-property-t
  - harder-function-field-s-arithmetic-cohomology-vanishing
  - sl3-polynomial-congruence-subgroups-have-large-b2
---

Notation as in the claim. `G_0 = SL_3(F_q((t)))`.

## 1. Density and one chamber

- **Density.** `A(f)` contains `e_ij(fa)` for all `a ∈ O_S`. `F_q[t,1/t]` is dense in `F_q((t))`,
  and `f` is a unit of `F_q[[t]]` because `f(0) ≠ 0`, so `f·O_S` is dense. Hence the closure of
  `A(f)` contains every `e_ij(λ)`, `λ ∈ F_q((t))`, and these generate `G_0`.
- **Orbits.** `G_0` acts type-preservingly on `X_0` and transitively on chambers. Let `σ` be a cell
  and `τ = gσ`, `g ∈ G_0`. The coset `g·Stab_(G_0)(σ)` is open, so it meets `A(f)` in some `a`, and
  `aσ = τ`. So `A(f)`-orbits of cells are `G_0`-orbits, and the quotient is the chamber `c`.
- **Stabilizers.** `O_S ∩ F_q[[t]] = F_q[t]` and `O_S/(f) = F_q[t]/(f)`, so
  `A(f) ∩ SL_3(F_q[[t]]) = Γ(f)`. For `v_i = g_i[O_0^3]` with `g_i ∈ GL_3(O_S)`, conjugation by
  `g_i` preserves `A(f)`, so `A(f)_(v_i) = g_iΓ(f)g_i^(-1)`.
  - The chamber stabilizer consists of the matrices of `Γ(f)` that are triangular mod `t`, so it
    contains `Γ(tf)`.
  - Links of vertices are finite, so every edge stabilizer has finite index in both of its vertex
    stabilizers.

## 2. Rows of the spectral sequence

Every cell stabilizer `A(f)_σ` has finite index in a conjugate `g_iSL_3(F_q[t])g_i^(-1)`.
- **Row 1.** `SL_3(F_q[t]) = EL_3(F_q[t])` (Euclidean ring) has (T) by
  `elementary-groups-over-fg-rings-have-property-t`, and so do its finite-index subgroups. So
  `H_1(A(f)_σ;Z)` is finite and `H^1(A(f)_σ;R) = 0`.
- **Rows `q >= 3`.** `g_i ∈ GL_3(F_q((1/t)))`, and `SL_3(F_q[t])` is discrete in `SL_3(F_q((1/t)))`.
  So `A(f)_σ` acts with finite stabilizers on the contractible 2-dimensional building `X_∞`, and
  `H^q(A(f)_σ;R) = H^q(A(f)_σ\X_∞;R) = 0` for `q >= 3`. This is the same comparison as in
  `sl3-polynomial-congruence-subgroups-have-large-b2-proof` §2 (Brown, *Cohomology of Groups*,
  Ch. VII; chapter-level pointer, not re-read).

## 3. The spectral sequence

- **Setup.** `X_0` is contractible. A type-preserving element that stabilizes a simplex fixes it
  pointwise, so orientation characters are trivial. The equivariant cohomology spectral sequence
  (Brown VII.7) gives `E_1^(p,q) = ∏_(σ ⊂ c, dim σ = p) H^q(A(f)_σ;R) => H^(p+q)(A(f);R)`, with `d_1`
  the alternating sum of restrictions. No conjugations enter, because the representatives are the
  faces of the one chamber `c` and `A(f)_c ⊆ A(f)_σ`.
- **Rows.**
  - Row 0 is the cochain complex of a 2-simplex, so `E_2^(0,0) = R` and `E_2^(1,0) = E_2^(2,0) = 0`.
  - Rows 1 and `q >= 3` vanish by §2.
  - Row 2 is (CH).
- **Degeneration.** `d_r : E_r^(p,q) -> E_r^(p+r,q-r+1)`. For `r >= 2`, a differential out of row 2
  lands in row 1 (zero) or in a column `p+r >= 3` (zero), and no differential enters row 2 from a
  nonzero row. So `E_2 = E_∞`, and each total degree has a single nonzero term. This gives the
  formulas of item 2.
- **Injectivity.** The edge map `H^2(A(f);R) -> E_∞^(0,2) ⊆ ⊕_i H^2(A(f)_(v_i);R)` is the product
  of the restrictions. Take `x = (x_0,x_1,x_2) ∈ ker d^0` with `x_0 = 0`, and let `e = {v_0,v_i}`.
  Then `x_i|_e = x_0|_e = 0`. Since `A(f)_e` has finite index in `A(f)_(v_i)`, restriction is
  injective on real cohomology (transfer), so `x_i = 0`.

## 4. Harder's theorem

`A(f)` is a congruence subgroup of `SL_3(O_S)`, `S = {0,∞}`, `r|S| = 4`. By
`harder-function-field-s-arithmetic-cohomology-vanishing`, `H^2(A(f);Q) = H^3(A(f);Q) = 0`. So
`d^0` is injective and `ker d^1 = im d^0`, and the sequence

```text
0 -> ⊕_i H^2_(v_i) -> ⊕_e H^2_e -> H^2_c -> H^4(A(f);R) -> 0
```

is exact. The alternating sum of dimensions vanishes, which is the `b_4` formula.
- The vertex groups are isomorphic to `Γ(f)`.
- Edge and chamber groups are conjugates of the preimages in `Γ(f)` of parabolic subgroups of
  `SL_3(F_q)` under reduction mod `t`; they contain `Γ(tf)`, so they are congruence subgroups.
- For `q = 2`, `f = t^2+1` is the image of `t^2` under the ring automorphism `t -> t+1`, so
  `b_2(Γ(f)) = 927`; for `f = t^2+t+1`, `b_2 = 1304` (table of
  `sl3-polynomial-congruence-subgroups-have-large-b2`).

## 5. Check at `f = 1` without Harder

Every cell stabilizer of `A` contains `A_c`, which contains `Γ(t)` with finite index. Under (S),
`b_2(Γ(t)) = 0` (same table). So `H^2(A_σ;R)` injects into `H^2(Γ(t);R) = 0`, row 2 vanishes, and
`H^*(A;R) = R`. This agrees with Harder's item 2 at level 1: the Steinberg multiplicity is `0`.
