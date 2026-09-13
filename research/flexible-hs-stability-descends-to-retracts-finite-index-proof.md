---
rg: 2
id: flexible-hs-stability-descends-to-retracts-finite-index-proof
kind: route
title: Compose with the retraction; for finite index, induce, round, and cut the first block out with a Kazhdan projection on the conjugation representation
target: flexible-hs-stability-descends-to-retracts-finite-index
requires: []
---

Norms `||·||_(2,n)` are normalized by `n`. `P` always denotes the coordinate co-isometry onto the
first `d` coordinates.

## 1. Retracts

- Let `α_n` be an asymptotic representation of `H`. Then `α_n∘r` is an asymptotic representation
  of `L`.
- By stability there are genuine `π_n : L -> U(D_n)`, `D_n/d_n -> 1`, with
  `||α_n(r(y)) - Pπ_n(y)P*|| -> 0` for all `y ∈ L`.
- Put `y = i(h)`. Then `π_n∘i` are genuine representations of `H` with
  `||α_n(h) - Pπ_n(i(h))P*|| -> 0`.

## 2. Finite index: induction

- **Setup.** Let `m = [Γ:H]`, with transversal `t_1 = e, t_2, ..., t_m`. For `g ∈ Γ` write
  `g t_i = t_(σ_g(i)) h(g,i)`, where `h(g,i) ∈ H`.
- **The induced model.** Given an asymptotic representation `α_n` of `H` on `C^(d_n)`, define
  `A_n(g)(e_i ⊗ v) = e_(σ_g(i)) ⊗ α_n(h(g,i))v` on `C^m ⊗ C^(d_n)`.
- **It is asymptotic.** Each defect of `A_n` at fixed `(g,g')` is a block-permutation of finitely
  many defects of `α_n`, so `A_n` is an asymptotic representation of `Γ`.
- **Block 1 is preserved.** For `h ∈ H` one has `σ_h(1) = 1` and `h(h,1) = h`. So `A_n(h)` commutes
  with the block projection `Q_1 = e_11 ⊗ 1`, and acts as `α_n(h)` on block 1.

## 3. Rounding the induced model

- **Rounding.** Stability of `Γ` gives genuine `π_n : Γ -> U(D_n)` with `D_n >= md_n`,
  `D_n/(md_n) -> 1`, and `||A_n(g) - Pπ_n(g)P*||_(2,md_n) -> 0` for all `g`.
- **Commutator bound.** Put `Q = P*Q_1P`, a rank-`d_n` projection in `M_(D_n)`. For `h ∈ H`, split
  `π_n(h)` into its compression `P*(Pπ_n(h)P*)P` plus terms supported on the `(D_n - md_n)`-dimensional
  complement of `P*P`. The complement terms have `||·||_(2,D_n)^2 <= 2(D_n - md_n)/D_n`. Since
  `A_n(h)` commutes with `Q_1`,

  ```text
  ||[π_n(h), Q]||_(2,D_n)  <=  2||A_n(h) - Pπ_n(h)P*||_(2,md_n) + 4((D_n - md_n)/D_n)^(1/2)  ->  0.
  ```

## 4. Kazhdan projection

- **Almost invariance.** `H` has finite index in a Kazhdan group, hence is Kazhdan. Fix a Kazhdan
  pair `(K,κ)` for `H`, and consider the conjugation representation `X -> π_n(h)Xπ_n(h)*` of `H` on
  `(M_(D_n), ||·||_(2,D_n))`. Here `||Q||_(2,D_n) = (d_n/D_n)^(1/2)`. By §3, `Q` is moved by at most
  `δ_n -> 0` over `K`.
- **Nearby commuting operator.** Let `T_n` be the orthogonal projection of `Q` onto the invariant
  subspace, which is the commutant `π_n(H)'`. The Kazhdan estimate gives
  `||T_n - Q||_(2,D_n) <= δ_n/κ`. The invariant subspace is `*`-closed, so `T_n` is self-adjoint.
- **Nearby commuting projection.** Put `E_n = 1_((1/2,∞))(T_n)`, which lies in `π_n(H)'`. For every
  projection `R`, `||T_n - R||_2^2 = ||T_n||_2^2 + tr((1 - 2T_n)R)`, and `E_n` minimizes this. So
  `||E_n - Q||_2 <= 2||T_n - Q||_2`.
- **Rank.** For projections, `|tr E_n - tr Q| <= ||E_n - Q||_2^2`. Hence
  `|rank E_n - d_n| <= 4D_nδ_n^2/κ^2`, which is `o(d_n)` because `D_n <= 2md_n` eventually.

## 5. The rounding of α_n

- **The genuine representation.** `ρ_n = π_n|H` restricted to `range E_n` is a genuine
  representation of `H`, since `E_n` commutes with `π_n(H)`.
- **Comparison map.** Let `V_n` be the partial isometry in the polar decomposition of `E_nQ`,
  mapping `range Q` into `range E_n`.
  - `||E_nQ - Q||_2 <= ||E_n - Q||_2`.
  - On the spectral subspace of `QE_nQ` above `1/2`, `V_n` differs from `E_nQ` by at most
    `C||E_n - Q||_2`.
  - The subspace below `1/2` has normalized rank `O(||E_n - Q||_2^2)`.
- **Error bound.** Identify `range Q` with `C^(d_n)`. Collecting the bounds, in the
  `d_n`-normalization,

  ```text
  ||α_n(h) - V_n* ρ_n(h) V_n||_(2,d_n)  <=  C m^(1/2) ( ||E_n - Q||_(2,D_n) + ||[π_n(h),Q]||_(2,D_n)
                                            + ||A_n(h) - Pπ_n(h)P*||_(2,md_n) ) + o(1).
  ```

- **Dimensions.** Pad `ρ_n` with a trivial summand, and move the small-rank part of `range Q` onto
  it. This gives a genuine representation on `C^(D'_n)` with `D'_n >= d_n` and `D'_n/d_n -> 1`,
  whose corner is within `o(1)` of `α_n(h)` for every `h` in a finite generating set of `H`. So `H`
  is flexibly HS-stable.
