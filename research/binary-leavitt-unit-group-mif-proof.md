---
rg: 2
id: binary-leavitt-unit-group-mif-proof
kind: route
title: Verify linear high transitivity and infinite rank for the Leavitt unit group on its Cantor module
target: binary-leavitt-unit-group-is-mif
requires:
  - linearly-transitive-groups-without-finite-rank-elements-are-mif
  - leavitt-algebras-l-k-1-n-are-simple
---

Fix `n >= 2`. Let `R = L_(F_2)(1,n)`, with generators `s_i, t_i` (`0 <= i <= n-1`) and
relations `t_i s_j = δ_ij`, `Σ_i s_i t_i = 1`. Let `C = {0..n-1}^N`, with cones
`[κ] = {κ w}` for finite words `κ`, and put `M = C(C, F_2)`, the locally constant
functions.

## 1. The Cantor module

Put `(s_i f)(a w) = δ_(a,i) f(w)` and `(t_i f)(w) = f(i w)`. These maps send locally
constant functions to locally constant functions. They satisfy:
- `(t_i s_j f)(w) = (s_j f)(i w) = δ_ij f(w)`;
- `(Σ_i s_i t_i f)(a w) = (t_a f)(w) = f(a w)`.

So `ρ : R -> End_(F_2)(M)` is a unital representation. Its kernel is a two-sided ideal
not containing `1`, so it is `0` by `leavitt-algebras-l-k-1-n-are-simple`. Hence
`U_n = R^×` embeds in `GL(M)`, and we identify elements of `R` with their operators.

For words `μ = μ_1...μ_K` put `s_μ = s_(μ_1) ... s_(μ_K)` and
`t_μ = t_(μ_K) ... t_(μ_1)`. By induction:
- `(s_μ f)(w) = f(w')` if `w = μ w'`, and `0` otherwise;
- `(t_μ f)(w) = f(μ w)`;
- `t_ν s_κ = δ_(νκ)` whenever `|ν| = |κ|`;
- `Σ_(|μ|=K) s_μ t_μ = 1`.

## 2. Depth-K functions and matrix units

Let `M_K <= M` be the functions constant on every cone `[κ]` with `|κ| = K`.
- **Basis.** The indicators `χ_κ` form a basis of `M_K`, so `dim M_K = n^K`.
- **Filtration.** `M_K <= M_(K+1)`, and `M` is infinite-dimensional.
- **Exhaustion.** `M = ∪_K M_K`: for locally constant `f`, the set `f^-1(1)` is clopen in
  the compact space `C`, hence a finite union of cones. Any `K` at least their lengths
  works.

Put `e_(μν) = s_μ t_ν` for `|μ| = |ν| = K`.
- **Matrix units.** By section 1, `e_(μν) e_(κλ) = δ_(νκ) e_(μλ)` and `Σ_μ e_(μμ) = 1`.
  So `D_K = span{e_(μν)}` is a unital subalgebra of `R`.
- **`D_K` is a full matrix algebra.** The unital homomorphism
  `M_(n^K)(F_2) -> D_K` sending matrix units to the `e_(μν)` is surjective, and injective
  because `M_(n^K)(F_2)` is simple. So `D_K ≅ M_(n^K)(F_2)` and
  `D_K^× ≅ GL_(n^K)(F_2) <= U_n`.
- **Action on `M_K`.** For `w = μ w'`, `(e_(μν) χ_κ)(w) = χ_κ(ν w') = δ_(νκ)`, and
  `e_(μν) χ_κ` vanishes off `[μ]`. So `e_(μν) χ_κ = δ_(νκ) χ_μ`. Hence `M_K` is
  `D_K`-invariant, and in the basis `(χ_κ)` the algebra `D_K` acts as all of
  `M_(n^K)(F_2)`. So `D_K^×` induces all of `GL(M_K)`.

## 3. Condition (E)

Let `A, B <= M` be finite-dimensional and `φ : A -> B` a linear isomorphism. By
section 2, `A + B <= M_K` for some `K`. Extend a basis of `A` and its image under `φ`
to bases of `M_K`, which gives `ψ ∈ GL(M_K)` extending `φ`. Pick `g ∈ D_K^× <= U_n`
inducing `ψ` on `M_K`. Then `g|_A = φ`.

## 4. Condition (R)

Here `F = F_2`, so `λ ∈ {0, 1}`. Let `g ∈ U_n`.
- **`λ = 0`.** `gM = M` is infinite-dimensional.
- **`λ = 1`, `g != 1`.** Let `I = {a ∈ R : dim aM < ∞}`. It contains `0`, is closed
  under sums, and satisfies `(ba)M ⊆ b(aM)` and `(ab)M ⊆ aM`. So `I` is a two-sided
  ideal. It does not contain `1` because `M` is infinite-dimensional, so `I = 0` by
  simplicity. Since `g - 1 != 0` in `R`, `(g - 1)M` is infinite-dimensional.

## 5. Conclusion

`U_n <= GL(M)` satisfies (E) and (R) over the finite field `F_2`, and `M` is
infinite-dimensional. By `linearly-transitive-groups-without-finite-rank-elements-are-mif`,
`U_n` is mixed-identity-free. ∎
