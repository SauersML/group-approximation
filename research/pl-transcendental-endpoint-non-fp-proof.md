---
rg: 2
id: pl-transcendental-endpoint-non-fp-proof
kind: route
title: Deforming the transcendental parameter turns a finite presentation into epimorphisms onto nearby groups, and a bump commutator that is trivial at λ but not nearby gives a contradiction
target: fp-pl-groups-with-f-have-no-transcendental-support-endpoints
artifacts:
  - research/artifacts/gq-bh-bh-free-32-order-rigidity.md
---

Lane proof, elementary, not independently reviewed. Notation as in the target. Work on `[0,1]`; the
circle case is identical after passing to lifts that commute with `x ↦ x+1`.

## Step 0: a generating set adapted to the hypotheses

Finite presentability does not depend on the finite generating set, so let
`X = {x_1, …, x_n, f_0, f_1, u}`, where the `x_i` generate `G`, `f_0, f_1` are the standard
generators of the copy of `F` on `D`, and `u` is the element of (E). Every generator's breakpoints,
slopes and intercepts lie in `Q(λ)`. Since `λ` is transcendental, each such number is `ρ(λ)` for a
unique rational function `ρ ∈ Q(t)`. Replacing `λ` by `t` defines, for each generator `x`, a
piecewise-affine map `x(t)`.

## Step 1: genericity (the key lemma)

**Every `ρ ∈ Q(t)` is either identically zero or nonzero at `λ`.** If `ρ(λ) = 0`, the numerator of
`ρ` has the transcendental root `λ`, so it is the zero polynomial.

**Lemma.** For every word `w` in `X^{±1}` there is an open interval `U_w ∋ λ` such that, for
`t ∈ U_w`, `w(t)` (the composite of the `x(t)`) is given by one fixed formula: finitely many pieces
whose endpoints, slopes and intercepts are fixed rational functions of `t`. In particular, if `w(λ)`
is the identity then `w(t)` is the identity for every `t ∈ U_w`.

*Proof.* Induction on the length of `w`. For a generator, the finitely many conditions saying
`x(t)` is an orientation-preserving PL homeomorphism of `[0,1]` are either polynomial identities
(continuity at breakpoints, `x(0) = 0`, `x(1) = 1`), which hold at `λ` and hence identically, or
strict inequalities (breakpoints increasing, slopes positive), which hold at `λ` and hence on a
neighborhood. For `w = y·w'` the pieces of `w` are cut out by the breakpoints of `w'` and the
preimages under `w'` of the breakpoints of `y`. All of these are rational functions of `t` on
`U_{w'} ∩ U_y`. Which piece of `y` contains which point is decided by the signs of finitely many
differences of these functions. Each difference is identically zero or nonzero at `λ`, so the nonzero
ones keep their sign on a smaller neighborhood `U_w`, and the combinatorics of the composition is
constant there. If `w(λ) = id`, every piece of `w(t)` has slope `σ(t)` with `σ(λ) = 1` and
intercept `τ(t)` with `τ(λ) = 0`, so `σ ≡ 1` and `τ ≡ 0` by genericity, and `w(t) = id` on
`U_w`. ∎

Two special cases are used below.
- `f_0, f_1` have rational data, so `f_i(t) = f_i` for every `t`. Hence `k(t) = k` for every word
  `k` in `f_0, f_1`, i.e. for every element of the copy of `F`, and every `t`.
- By the Lemma applied to `u`, `u(t)` is a one-bump homeomorphism with support `(a(t), e(t))`
  for `t` near `λ`, where `a, e ∈ Q(t)` and `a(λ) = a`, `e(λ) = e`. The one-bump property is a
  finite set of strict conditions on each piece: no solution of `σ s + τ = s` inside the piece, or
  `σ = 1` with `τ ≠ 0`. These persist near `λ`.

## Step 2: a finite presentation gives epimorphisms onto nearby groups

Suppose `G = ⟨X | r_1, …, r_k⟩`. Let `U` be the intersection of the `U_{r_j}`, of `U_x` for
`x ∈ X`, and of a neighborhood on which `u(t)` is one-bump with support in the interior of `D`.
For `t ∈ U`, every `r_j(t)` is the identity by the Lemma. So, by von Dyck's theorem, `x ↦ x(t)`
extends to a homomorphism `φ_t: G → PL([0,1])` with `φ_t(w(λ)) = w(t)` for every word `w`.

## Step 3: a relation that holds at λ but fails nearby

`e ∉ Q`, so `e(t)` is a non-constant rational function. Its derivative is a nonzero element of
`Q(t)`, hence nonzero at `λ`, so `e(t)` is strictly monotone near `λ`. Pick `t ∈ U` with
`e(t) > e(λ)`, and a dyadic rational `r` with `e(λ) < r < e(t)`. Shrinking `U` if needed, we may
assume `a(t) < e(λ)`.

Let `k_r` be an element of the copy of `F` that is a one-bump homeomorphism with support exactly
`(r, d_1)`. Such elements exist in `F` for every dyadic `r` in the interior of `D`. Put
`w = u k_r u^{-1} k_r^{-1}`.

- **At `λ`.** The supports `(a, e)` and `(r, d_1)` are disjoint (`e < r`), so `u` and `k_r`
  commute and `w(λ) = id`.
- **At `t`.** `k_r(t) = k_r`, and `u(t)` has support `(a(t), e(t))` with `a(t) < r < e(t) < d_1`.
  Then `u(t) k_r u(t)^{-1}` has support `u(t)((r, d_1)) = (u(t)(r), d_1)`, since `u(t)` fixes
  `d_1`. Also `u(t)(r) ≠ r`, because `r` lies inside the support of the one-bump map `u(t)`.
  So `u(t) k_r u(t)^{-1} ≠ k_r`, i.e. `w(t) ≠ id`.

But `φ_t(w(λ)) = w(t)`, and `w(λ) = id` forces `w(t) = id`. This contradiction shows `G` is not
finitely presented. ∎

## Remarks

- For the left endpoint, use `k_r` with support `(d_0, r)`.
- For the "equivalent hypothesis" of the target: if `g` is affine on `I ⊂ D` with `g(I) ⊂ D`, slope
  `σ(λ)` and intercept `τ(λ)` not both rational, take an `F`-bump `k` with support `(r', s') ⊂ I`
  (dyadic). Then `g k g^{-1}` is a one-bump element with support `(g(r'), g(s'))`. Its right endpoint
  `σ s' + τ` is rational for at most one value of `s'` unless `σ` and `τ` are both constant, so for a
  suitable dyadic `s'` it is irrational.
- **Inputs.** Only von Dyck's theorem, invariance of finite presentability under change of finite
  generating set, the existence of one-bump elements of `F` with prescribed dyadic support, and the
  transcendence of `λ`. No literature theorem is imported.
