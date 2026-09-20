---
rg: 2
id: lifted-thompson-t-twisted-witnesses-need-unbounded-lie-closure
kind: claim
title: "Exact K(3,4)-representations whose Lie closure has semisimple part of dimension <= N and whose T-bar defect is below min(1/2, delta_N/2) are abelian, of the form x -> T^3, y -> T^4, with ||sigma(c) - 1|| <= 12 D; so T-bar non-MF witnesses with nontrivial scalar twist need unbounded Lie closure, and every fixed-compact-group amplification dies"
distinct_from:
  thompson-v-gap-witnesses-need-unbounded-lie-closure: that is the untwisted gap for V over S4 * S3; this is its transplant to T over Z4 * Z3 and, mainly, the twisted version for T-bar over K(3,4), where the central element moves and the adjoint representation is the device that removes it.
  thompson-gap-witnesses-need-nonamenable-image: that kills virtually solvable images; this kills every image whose closure has bounded semisimple part, which includes all compact Lie images of fixed dimension, and it controls the twist sigma(c).
  thompson-t-mf-iff-opnorm-z4-z3-defect-gap-vanishes: that shows T is MF iff delta_n -> 0; this uses delta_n as an input and bounds the T-bar defect of twisted representations by the untwisted T gap at the semisimple dimension of the Lie closure.
  lifted-thompson-t-is-not-mf: that is the flagship; this is a class-kill for witnesses against it and does not decide it.
  lifted-thompson-t-is-a-quotient-of-a-brieskorn-lattice: that kills triangle-local arguments for relative (T) of the centre; this kills bounded-Lie-closure amplification of exact K(3,4)-representations, including those factoring through the Brieskorn lattice.
artifacts:
  - experiments/lifted-t-lie-closure-gap-2026-09-17/check_twisted_adjoint.py
  - experiments/lifted-t-lie-closure-gap-2026-09-17/out_check_twisted_adjoint.json
---

**ESTABLISHED (written proof; not Lean-verified).**  Proof route:
`lifted-t-twisted-witnesses-lie-closure-proof`.

## Notation

- `K = K(3,4) = <x, y | x^4 = y^3>`, with `c = x^4` central.
- Over `K`, `T̄` has the relators
  - `rho1 = [yxy, x^2 yxy x^2]`,
  - `rho2 = [yxy, x^2 y^2 x^2 yxy x^2 y x^2]`,
  - `rhoP = (yx)^5 x^(-12)`.

  Put `Γ̂ = K / <<rho1, rho2, rhoP>>`.  Then `Γ̂ ≅ T̄`, with `c ↦ z` (item 0 of the proof).
- `G0 = Z4 * Z3 = <α, β>`, and `T = G0 / <<r1, r2, rP>>`.  Here `r1, r2` are the same
  commutator words in `α, β`, and `rP = (βα)^5`
  (`thompson-t-lochak-schneps-presentation`).
- An *exact `K`-representation* is a unitary `σ : K → U(n)`.
- `D(σ) = max_i ||σ(ρ_i) - 1||` is its `T̄` defect (operator norm).
- For a `G0`-representation `τ`, `D_T(τ) = max_i ||τ(r_i) - 1||` is its `T` defect.
- `δ_N` is the least `T` defect of a nontrivial `G0`-representation of dimension `<= N`.
  Set `δ_0 = +∞`.  By `thompson-t-mf-iff-opnorm-z4-z3-defect-gap-vanishes`, `T` is MF iff
  `δ_N → 0`.
- `K_σ` is the closure of `σ(K)`, a compact Lie group, and `l` is its Lie algebra.
  `N_σ := dim_R [l, l]` is the dimension of the semisimple part of `l`.

## Statement

**(1) T transplant.**  Every nontrivial `G0`-representation `τ` satisfies
`D_T(τ) >= min(1/2, δ_{N_τ}/2)`, where `N_τ` is defined from `τ(G0)` in the same way.
Moreover, `D_T(τ) >= √2` if `τ` is irreducible and imprimitive.

**(2) T̄ twisted gap.**  Let `σ` be an exact `K`-representation with

```text
D(σ) < min(1/2, δ_{N_σ}/2).
```

Then:
- `σ(K)` is abelian.
- `σ(x) = T^3` and `σ(y) = T^4`, where `T = σ(x)^(-1) σ(y)`.
- `σ(rhoP) = T^(-1)` and `σ(c) = T^12`.
- Hence `||σ(c) - 1|| <= 12 D(σ)`.

The constant `12` is asymptotically sharp, on the characters `x ↦ t^3`, `y ↦ t^4` as
`t → 1`: the ratio is `11.99999928` at `arg t = 1e-4`.

**(3) Twisted witnesses need unbounded Lie closure.**  Let `(A_n, B_n)` be pairs in `U(k_n)`
and `μ_n` scalars with `|μ_n - 1| >= ε > 0` and

```text
η_n := max(||A_n^4 - μ_n||, ||B_n^3 - μ_n||) → 0.
```

Let `D_n` be the `T̄` defect of the pair.  This is an asymptotic representation of `T̄` with
scalar twist `z ↦ μ_n`.

Round spectrally to exact `K`-representations `σ_n` with `σ_n(c) = μ_n` (item 3 of the
proof).  Then `D(σ_n) <= D_n + O(η_n)`.

Let `N` bound `N_{σ_n}` along some subsequence.  Then, along that subsequence,

```text
D_n  >=  min(1/2, δ_N/2, ε/12) - O(η_n),
```

and `δ_N > 0` for each fixed `N` (item 1 of the proof).  So **every sequence with
`D_n → 0` and nontrivial scalar twist has `N_{σ_n} → ∞`.**

**(4) Class kill: fixed-compact-group amplification.**  Every family

```text
σ_j = π_j ∘ φ,   φ : K → M
```

has `N <= dim M`.  Here `M` is a fixed compact group and `π_j` are arbitrary unitary
representations of `M`, for example tensor powers, `Sym^m`, induced or random
representations of `M`.  So the family obeys the uniform bound of (3).

- **Named invariant:** `dim_R [l, l]`, the semisimple dimension of the Lie closure.  It
  does not increase under `π_j`.
- **Death step:** the adjoint transfer `τ = Ad ∘ σ` on `[l, l]_C`.  It has dimension
  `<= dim M`, kills `c`, and has `T` defect `<= 2D`.  So `D < δ_{dim M}/2` forces `τ = 1`.

This kills, for twisted `T̄` witnesses:
- `Sym^m` and tensor amplification of a fixed `SU(2)`-, `SO(3)`- or `SU(d)`-pair with
  `A^4 = B^3`;
- all finite and virtually solvable quotients of `K`, including the finite quotients of the
  Brieskorn lattice `Λ`.  Here the closure has torus identity component, so `N = 0`,
  `δ_0 = ∞`, and (2) reads: `D < 1/2` forces an abelian representation with twist `<= 12 D`;
- random matrix models whose samples live in one fixed compact group, such as Haar pairs in
  `U(d)` pushed through representations of `U(d)` with `d` fixed.

## Evidence (artifacts)

The script `check_twisted_adjoint.py` (numpy, seed 20260920) gives the following.
- **Twisted line.**  `rho1 = rho2 = 1` and `rhoP · t = 1` exactly.  The ratio
  `|t^12 - 1| / D` is `11.30, 11.993, 11.99993, 11.9999993` at
  `arg t = 1e-1, …, 1e-4`.
- **Adjoint transfer.**  200 random exact scalar-twisted pairs in `U(2..5)`.
  `Ad(A)^4 = Ad(B)^3 = 1` exactly, and `max D_T(Ad∘σ) / (2 D(σ)) = 0.833 <= 1`.
- **`Sym^m` of SU(2) pairs, m = 1..24.**  Here `A^4 = B^3 = -1`, and `D` is minimised over the
  axis angle.
  - `m = 1` gives `D = 2 sin(π/24) = 0.2611`.  This twisted pair is nonabelian, so it is
    consistent with (2) only if `δ_3 <= 0.522`.
  - `m = 2` is an exact `SO(3)`-representation of `G0` with `D_T = 2 sin(π/12) = 0.5176`.
    That bound on `δ_3` is weaker than the value `δ_2 ≈ 0.349` found numerically by another
    worker in this wave, and it is not claimed as new.
  - So the factor `2` of the adjoint transfer is nearly attained (`0.5176 / 0.2611 = 1.98`).
  - For `m >= 2` the minimum is `>= 2 sin(π/12)` and grows towards `2`.

## What this changes

- **For `lifted-thompson-t-is-not-mf`.**  By the twist-set dichotomy landed elsewhere in this
  wave, a non-MF witness for `T̄` is a corona representation with nontrivial central twist.
  This node shows the following.
  - Such a witness, after scalar rounding, cannot come from any compact group of bounded
    dimension, nor from any finite or virtually solvable quotient of `K(3,4)`.
  - The twist is controlled linearly by the defect, `||σ(c) - 1|| <= 12 D`, as long as the
    semisimple Lie closure stays below the `T` gap.
  - A witness must therefore do two things at once:
    - make the `T` gap `δ_N` small at the semisimple dimension `N` of its own closure, which is
      MF-type behaviour of `T` itself;
    - keep the twist `>= ε`.
  - So **a disproof of the flagship needs `T` to be MF-like at growing dimension**, with the
    twist carried by the unbounded semisimple part.
- **Explains the twisted character line.**  The only low-defect twisted `K`-representations
  below the gap are the characters `x ↦ t^3`, `y ↦ t^4`.  There the twist is `t^12` and the
  defect is `|t - 1|`, and both go to zero together.  This is the rigorous version of the
  observation that twisted characters of `K` "untwist in the limit".
- **Not claimed.**
  - No lower bound on `δ_N` is proved here.  If `T` is not MF, then `δ_N >= δ > 0` for all `N`,
    and (2) holds with the uniform constant `min(1/2, δ/2)` in every dimension, with no Lie
    closure hypothesis.
  - Non-scalar twists, where `ρ(z)` is not scalar in `U(k_n)`, reduce to the scalar case only
    after cutting by an eigencorner.  That is the open (EC) step of
    `lifted-thompson-t-centre-has-commutant-eigencorners`, and it is not used here.
