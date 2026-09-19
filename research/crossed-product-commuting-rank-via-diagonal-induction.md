---
rg: 2
id: crossed-product-commuting-rank-via-diagonal-induction
kind: route
title: Tensor a kΓ-resolution of k with a module under the diagonal action; the free terms are induced from the von Neumann regular diagonal, so they are flat
target: cantor-crossed-products-bound-commuting-rank-by-cd
requires: [polynomial-subrings-bound-transcendental-flat-dimension]
---

All unmarked tensor products are over `k`. Fix a field `K ⊇ k`. Put `D = LC(X, K)`, a commutative unital ring,
and `B = D ⋊ Γ`, with `u_g d u_g^(-1) = g·d`. As a right `D`-module, `B = ⊕_g u_g D` is free.

## 1. `D` is von Neumann regular

Every `f ∈ D` takes finitely many values on a finite clopen partition of `X`. So `D` is the directed union of the
finite products `K^m` of those partitions. Each `K^m` is von Neumann regular, hence so is `D`. So every
`D`-module is flat.

## 2. The diagonal module

Let `0 -> P_s -> ... -> P_0 -> k -> 0` be a projective resolution over `kΓ`, and `M` a left `B`-module. Let `B`
act on `P_j ⊗ M` by

`d · (p ⊗ m) = p ⊗ dm`, and `u_g · (p ⊗ m) = gp ⊗ u_g m`.

This is a `B`-module: `u_g d u_g^(-1)` sends `p ⊗ m` to `p ⊗ u_g d u_g^(-1) m = p ⊗ (g·d) m`, as required. The
differentials `∂ ⊗ 1` are `B`-linear. Over the field `k`, `P_• ⊗ M -> k ⊗ M = M` stays exact.

## 3. The free terms are flat

**Lemma.** `kΓ ⊗ M`, with the action of Section 2, is isomorphic to `B ⊗_D M`.

*Proof.* `B ⊗_D M = ⊕_g u_g ⊗ M`. Define `Φ(u_g ⊗ m) = g ⊗ u_g m`. It is bijective, since each `u_g` acts
bijectively on `M`.
- *`D`-balanced.* `u_g d ⊗ m` and `u_g ⊗ dm` both go to `g ⊗ u_g d m`.
- *`u_h`-linear.* `u_h u_g ⊗ m = u_(hg) ⊗ m ↦ hg ⊗ u_(hg) m = u_h · (g ⊗ u_g m)`.
- *`D`-linear.* `d u_g ⊗ m = u_g (g^(-1)·d) ⊗ m ↦ g ⊗ u_g (g^(-1)·d) m = g ⊗ d u_g m = d · (g ⊗ u_g m)`. ∎

**Flatness.** For a right `B`-module `N`, `N ⊗_B (B ⊗_D M) = N ⊗_D M`. This is exact in `N`, because `M` is
flat over `D` (Section 1). So `B ⊗_D M` is flat over `B`.
- A free `kΓ`-module gives a direct sum of copies of `kΓ ⊗ M`, which is flat.
- A projective `kΓ`-module is a summand of a free one, so `P_j ⊗ M` is a summand of a flat module, hence flat.

So `P_• ⊗ M` is a flat resolution of length `s` of `M`, and `w.gl.dim B <= s`.

## 4. The commuting-rank bound

- `LC(X, k) ⊗ K = LC(X, K)`, since locally constant functions on compact `X` have finite range. So
  `A ⊗ K = LC(X, K) ⋊ Γ = B`.
- `M_r(A) ⊗ K ≅ M_r(B)`, and weak global dimension is Morita invariant, since an equivalence of module
  categories given by tensoring with a progenerator preserves Tor. So `w.gl.dim(M_r(A) ⊗ K) <= s`.
- If `M_r(A)` had a commuting independent family of size `n`, then with `K = k(y_1, ..., y_n)` the claim
  `polynomial-subrings-bound-transcendental-flat-dimension` gives `n <= w.gl.dim(M_r(A) ⊗ K) <= s`.

Non-unital maps are handled by Section 4 of `polynomial-subring-flat-dimension-via-fraction-field-koszul`. ∎

## 5. Resolutions used in the instances

- `Γ = Z^m`: the Koszul complex on `t_1 - 1, ..., t_m - 1` over `k[Z^m]`, of length `m`.
- `Γ = F_d`: `0 -> kF_d^d -> kF_d -> k -> 0`, from the augmentation ideal being free on the `g_i - 1`.
- `Γ = Γ_1 × Γ_2`: the tensor product over `k` of resolutions for the factors. It is exact by Künneth over a
  field, and its terms are projective over `kΓ_1 ⊗ kΓ_2 = k[Γ_1 × Γ_2]`. So `Z^2 × F_d` has `s = 3`.
