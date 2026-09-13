---
rg: 2
id: character-rigid-fp-simple-stability-dictionary-proof
kind: route
title: Limit characters of almost actions are rigid, amplification separates, and stability forces residual finiteness
target: character-rigid-fp-simple-groups-stability-dictionary
requires:
  - finitely-presented-lef-groups-are-residually-finite
  - hyperlinear-flexibly-hs-stable-group-is-residually-finite
  - finitely-generated-linear-groups-are-residually-finite
  - hyperlinear-iff-group-factor-embeds-in-hyperfinite-ultrapower
artifacts:
  - research/artifacts/thompson-v-soficity-stability-and-full-groups-2026-09-12.md
---

Throughout, `Γ` is finitely presented, infinite and simple, with character simplex
`{t τ_reg + (1-t) τ_triv}`. Fix a nonprincipal ultrafilter `ω`.

**Lemma 0.** `Γ` is not residually finite, not LEF, and has no nontrivial finite-dimensional
unitary representation.
- **Not residually finite.** A residually finite infinite group has a proper nontrivial
  finite-index normal subgroup, which simplicity forbids.
- **Not LEF.** By `finitely-presented-lef-groups-are-residually-finite`, a finitely presented
  LEF group is residually finite.
- **No finite-dimensional representations.** The image of a representation
  `ψ : Γ -> U(d)` is finitely generated and linear, so it is residually finite
  (`finitely-generated-linear-groups-are-residually-finite`). By simplicity `ker ψ` is `1` or `Γ`.
  If it were `1`, then `Γ` would be residually finite, so `ψ` is trivial.

## (P) Permutations

Bradford's Remark 1.5 gives `2 => 3`, `2 => 4`, `3 => 5` and `4 => 5`. Also `6 => 2`,
since the trivial homomorphisms witness stability.

**`5 => 1`.** Suppose `Γ` is sofic and weakly locally stable.
1. Soficity gives a separating almost-homomorphism `φ_n`: `d(φ_n(g), id) -> 1` for `g != e`.
2. Weak local stability gives partial homomorphisms `ψ_n` with `d(φ_n(g), ψ_n(g)) -> 0`. For
   every `g, h` there is `N` with `ψ_n(gh) = ψ_n(g) ψ_n(h)` for `n >= N`.
3. Fix a finite set `B` and choose `n` past the thresholds for all pairs in `B` and with
   `d(ψ_n(g), id) > 1/2` for every `g != e` in `B`.
4. Then `ψ_n` is multiplicative on `B` and sends no nontrivial element of `B` to the identity,
   so it is injective on `B`. That is a local embedding of `B` into the finite group `Sym(k_n)`.
5. So `Γ` is LEF, contradicting Lemma 0.

**`1 => 6`.** Let `φ_n` be an almost-homomorphism, and put
`χ(g) = lim_ω |Fix(φ_n(g))| / k_n`.
- **`χ` is a normalized character.** `φ_n(e)^2 ≈ φ_n(e)` forces `φ_n(e) ≈ id`, so `χ(e) = 1`.
  Bi-invariance of the Hamming metric makes `χ` a class function. It is positive definite by the
  identity
  ```text
  Σ_(i,j) c_i conj(c_j) |Fix(σ_j^(-1) σ_i)|  =  Σ_(x,y) | Σ_i c_i [σ_i x = y] |^2  >=  0,
  ```
  with `σ_i = φ_n(g_i)`, whose error against `|Fix(φ_n(g_j^(-1) g_i))|` is `o(k_n)`.
- **Rigidity.** So `χ = t τ_reg + (1-t) τ_triv`.
- **Amplification, if `t > 0`.** Let `φ_n^(m)` act coordinatewise on `[k_n]^m`. Its defect is at
  most `m` times that of `φ_n`, by a union bound over coordinates. For `g != e`, its fixed-point
  fraction tends along `ω` to `(1-t)^m`. Diagonalizing over finite subsets of `Γ` and `m -> ∞`
  gives a separating almost-homomorphism, so `Γ` is sofic.
- **Conclusion.** Under (1), `t = 0` along every `ω`. So `|Fix(φ_n(g))| / k_n -> 1`, that is
  `d(φ_n(g), id) -> 0`.

## (U) Unitaries

`4 => 2`: the trivial representations are genuine. `2 => 3`: strict stability is flexible
stability with `D_n = d_n`.

**`3 => 1`.** By `hyperlinear-flexibly-hs-stable-group-is-residually-finite`, a finitely generated
hyperlinear flexibly HS-stable group is residually finite, contradicting Lemma 0.

**`1 => 4`.** Let `π_n` be an asymptotic representation, and put `χ(g) = lim_ω tr π_n(g)`, with
`tr` the normalized trace.
- **`χ` is a normalized character.**
  - `χ(e) = 1`: `π_n(e)` is an almost-idempotent unitary, hence `≈ 1`.
  - Class function: `||π_n(hgh^(-1)) - π_n(h) π_n(g) π_n(h)^*||_2 -> 0`, `tr` is unitarily
    invariant, and `|tr X| <= ||X||_2`.
  - Positive definite: `Σ c_i conj(c_j) tr(π_n(g_j)^* π_n(g_i)) = tr(Y^* Y) >= 0` with
    `Y = Σ c_i π_n(g_i)`, and `π_n(g_j^(-1) g_i) ≈ π_n(g_j)^* π_n(g_i)` in `||·||_2`.
- **Rigidity.** So `χ = t τ_reg + (1-t) τ_triv`.
- **Amplification, if `t > 0`.** Put `π_n^(m) = π_n^(⊗m)` on `(C^(d_n))^(⊗m)`. The normalized HS
  norm is multiplicative on tensor products, and unitaries have norm `1`. Telescoping gives
  `||A^(⊗m) B^(⊗m) - C^(⊗m)||_2 = ||(AB)^(⊗m) - C^(⊗m)||_2 <= m ||AB - C||_2` for unitaries, so
  the defect grows at most `m`-fold. The normalized trace is multiplicative, so
  `tr π_n^(m)(g) -> (1-t)^m` along `ω` for `g != e`. A diagonal sequence over `m -> ∞` and finite
  subsets of `Γ` gives microstates with `tr -> δ_(g,e)`. By
  `hyperlinear-iff-group-factor-embeds-in-hyperfinite-ultrapower` (3 => 1), `Γ` is hyperlinear.
- **Conclusion.** Under (1), `t = 0` along every `ω`. So `tr π_n(g) -> 1`, and
  `||π_n(g) - 1||_2^2 = 2 - 2 Re tr π_n(g) -> 0`.
