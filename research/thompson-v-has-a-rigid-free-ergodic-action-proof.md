---
rg: 2
id: thompson-v-has-a-rigid-free-ergodic-action-proof
kind: route
title: Gaussian functoriality carries rigidity and weak mixing, a first-chaos variable kills fixed sets, and V moves cylinders onto proper subcylinders
target: thompson-v-has-a-rigid-free-ergodic-action
requires: []
---

Notation as in the target. For `v ∈ H` let `X_v` be the centred Gaussian variable of the Gaussian space, with
`E[X_v X_w] = <v, w>`. The action satisfies `X_v(g^-1.ω) = X_(π(g) v)(ω)` for a.e. `ω`, and
`L^2(Ω, γ) = ⊕_(n≥0) Sym^n(H)` with Koopman representation `⊕_n Sym^n(π)`.

**General principle.**
- **Rigid.** `π(g_n) → 1` strongly gives `Sym^n(π(g_n)) → 1` on elementary symmetric tensors, hence strongly on
  each `Sym^n(H)`, since the operators are uniformly bounded. The same holds on the direct sum. So
  `γ(g_n A Δ A) = ‖1_(g_n A) − 1_A‖^2 → 0` for every measurable `A`.
- **Ergodic.** An invariant vector in `L^2_0(Ω)` lies in some `Sym^n(H) ⊆ H^(⊗n)`, `n ≥ 1`. A tensor product
  with a representation having no finite-dimensional invariant subspace has no invariant vectors. So
  `L^2_0(Ω)` has none, and the action is ergodic.
- **Free.** Let `g ≠ 1`. `π` is faithful, so `π(g) v ≠ v` for some `v`. On `Fix(g)`, `X_(π(g) v) = X_v`
  a.e., so `X_w = 0` with `w = π(g) v − v ≠ 0`. `X_w` is a non-degenerate Gaussian, so `γ(Fix(g)) = 0`.
  `Γ` is countable, so the action is essentially free.

**Thompson's V.** Elements of `V` map cylinders onto cylinders affinely, so the Radon–Nikodym derivative is a
locally constant power of 2 and `κ` is orthogonal.
- **Faithful.** If `κ(g) = 1`, then `κ(g) 1_([w]) = 1_([w])` forces `g[w] = [w]` up to null sets. Both are
  clopen and `µ` has full support, so `g[w] = [w]` for every cylinder `[w]`, and `g = 1`.
- **No finite-dimensional invariant subspace.** Let `W ≠ 0` be finite-dimensional and invariant. `V` is finitely
  generated, so its image in `O(W)` is a finitely generated linear group, hence residually finite (Malcev). `V` is
  infinite and simple, hence not residually finite, so the image is trivial and `W` consists of invariant vectors.
  Let `f ≠ 0` be invariant. Then `ν = f^2 µ` is a finite `V`-invariant measure, absolutely continuous with respect
  to `µ`. The element `0w ↦ 00w`, `10w ↦ 01w`, `11w ↦ 1w` lies in `V` and maps `[0]` onto `[00]`, so
  `ν([00]) = ν([0]) = ν([00]) + ν([01])` and `ν([01]) = 0`. `V` maps `[01]` onto every proper cylinder, so every
  proper cylinder is `ν`-null and `ν = 0`, contradicting `f ≠ 0`.
- **Rigidity sequence.** `t_n` swaps `0^n 0 w ↔ 0^n 1 w` and fixes points outside `[0^n]`. It preserves `µ`, so
  `κ(t_n) f − f` vanishes off `[0^n]` and `‖κ(t_n) f − f‖ ≤ 2 ‖f · 1_([0^n])‖ → 0`. The `t_n` are distinct, so
  they leave every finite set.

The general principle applies to `κ`.
