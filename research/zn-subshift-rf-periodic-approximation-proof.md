---
rg: 2
id: zn-subshift-rf-periodic-approximation-proof
kind: route
title: Color a finite approximating orbit by the symbols at the origin to get a periodic configuration with legal windows, and conversely lift the points of periodic models to distinct points of X
target: zn-subshift-is-rf-iff-periodically-approximable
requires: []
---

Notation as in the target. `B_r = {v : |v|_∞ <= r}`. The residual-finiteness definition is Ma's Def. 5.1 (Kerr–Nowak),
quoted in `rf-free-minimal-zn-non-fp-proof`. An **`r`-model family** is a finite set of configurations `y^1, …, y^m`
satisfying (M1) and (M2), such that every `r`-pattern of `X` occurs in some `y^j` (M3′).

## Item 1, "only if"

- **Setup.** Fix `r` and take `F = B_r` and `ε < 1`. Residual finiteness gives an `ε`-dense finite `E ⊆ X` and a
  `Z^N`-action `β` on `E` with `d(σ^u z, β(u)z) < ε`, hence `(β(u)z)_0 = (σ^u z)_0 = z_u`, for all `z ∈ E` and
  `u ∈ B_r`. Here `σ` is the shift.
- **The configurations.** For `p ∈ E` put `y^p_v = (β(v)p)_0`. Since `β` is an action on the finite set `E`, `y^p` is
  invariant under the finite-index subgroup `Stab_β(p)`: (M1).
- **(M2).** For `v ∈ Z^N` and `u ∈ B_r`, put `q = β(v)p ∈ E`. Then `y^p_(v+u) = (β(u)q)_0 = q_u`. So
  `y^p|_(v+B_r) = q|_(B_r)`, a pattern of `X`.
- **(M3′).** Take also `ε < 2^(−r)`. Then `E` is `2^(−r)`-dense, so every `r`-pattern of `X` equals `q|_(B_r)` for some
  `q ∈ E`, and `q|_(B_r) = y^q|_(B_r)`, taking `p = q` and `v = 0` above. So `{y^p : p ∈ E}` is an `r`-model family.
- **One model suffices for minimal `X`.** A minimal subshift is uniformly recurrent: there is `R` such that every
  `R`-pattern of `X` contains every `r`-pattern of `X`. A single configuration `y^p` from the family at radius `R`
  already has all its `R`-windows equal to `X`-patterns, so it contains every `r`-pattern.

## Item 1, "if"

- **Setup.** Given finite `F` and `ε > 0`, choose `r` with `2 max_(s∈F) |s|_∞ <= r` and `2^(−r/2) < ε`, and an
  `r`-model family `y^1, …, y^m`.
- **The finite set.** Let `W` be the disjoint union of the finite orbits `Z^N · y^j`, with its `Z^N`-action. For each
  `w ∈ W` choose `z_w ∈ X` agreeing with `w` on `B_r`, which is possible by (M2). Choose the `z_w` pairwise distinct:
  `X` is perfect, so nonempty cylinders are infinite. Let `E = {z_w}`, with `β(s) z_w := z_(s·w)`, a `Z^N`-action on
  `E`.
- **Closeness.** For `s ∈ F`, both `σ^s z_w` and `z_(s·w)` agree with `s·w` on `B_(r/2)`, since `r − |s| >= r/2`. So
  `d(σ^s z_w, β(s) z_w) <= 2^(−r/2) < ε`.
- **Density.** For `x ∈ X`, its `r`-pattern occurs in some `w ∈ W` by (M3′), so `d(x, z_w) <= 2^(−r)`. ∎

## Item 2

- Let `r_0` bound the size of the forbidden patterns of `Y`. If `X ⊆ Y` were residually finite, "only if" at
  `r >= r_0` would give a configuration `y^p` of finite orbit whose `r`-windows are all patterns of `X ⊆ Y`.
- So `y^p` contains no forbidden pattern, `y^p ∈ Y`, and `Y` has a configuration of finite orbit. This contradicts weak
  aperiodicity.
- A nonempty SFT contains a minimal subsystem, by Zorn and compactness. If `Y` is strongly aperiodic, that subsystem is
  free. It is infinite, having no finite orbits, and a minimal infinite subshift is perfect. ∎

## Item 3, "if" direction (all that is used)

Let `X = lim X_k`, with factor maps `π_k : X → X_k` onto subshifts, and suppose each `X_k` is residually finite.
- **Choice of scale.** Given `F` and `ε`, choose `k` and `δ` such that `d_k(π_k x, π_k x') < δ` implies `d(x,x') < ε`.
  This holds for the standard inverse-limit metric once `k` is large, by uniform continuity of the finitely many
  earlier factor maps.
- **The approximation.** Take `E_k ⊆ X_k` and `β_k` for `(F, δ)`, and lift `E_k` injectively to `E ⊆ X`. Distinct
  points of `X_k` have disjoint fibers. Put `β(s)(lift z) = lift(β_k(s) z)`.
- **Checks.** Both closeness and density are statements about pairs of points with `δ`-close `π_k`-images, so they
  hold with `ε`.

The converse is not claimed. ∎
