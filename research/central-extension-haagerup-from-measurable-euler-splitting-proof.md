---
rg: 2
id: central-extension-haagerup-from-measurable-euler-splitting-proof
kind: route
title: "Skew product X × R: z acts by unit translation, flat bump vectors give coefficients that decay along cosets of <z>; multiply by C_0 functions of Q"
target: central-extension-haagerup-from-measurable-euler-splitting
requires: []
---

Notation as in the target. Imports, all standard:
- (I1) Akemann–Walter: a countable group has the Haagerup property iff there are normalized
  positive definite `C_0` functions `Φ_j` with `Φ_j → 1` pointwise.
- (I2) Products of positive definite functions are positive definite.
- (I3) The Koopman representation of a nonsingular action is a unitary representation.
  The chain rule `RN_{gh}(x) = RN_g(x) RN_h(g^{-1}x)` holds a.e.

**Step 0 (positive vectors).** `|⟨κ(q)|ξ|, |ξ|⟩| ≥ |⟨κ(q)ξ, ξ⟩|` because `RN_q ≥ 0`. And for unit
vectors, `‖κ(q)ξ − ξ‖² = 2 − 2 Re⟨κ(q)ξ, ξ⟩`. So we may take `ξ_n ≥ 0`.

**Step 1 (skew product).** `Q` is countable and nonsingular maps preserve null sets. So after
discarding one null set, the cocycle identity and `β(z, ·) = 1` hold everywhere on a conull
`G`-invariant set. Then the cocycle identity gives, for all `m ∈ Z`:
- `β(z^m, x) = m`;
- `β(g z^m, x) = β(g, x) + m`, using that `z` acts trivially on `X`.

Let `G` act on `Ω = X × R` by `g·(x, t) = (gx, t + β(g, x))`. The cocycle identity makes this an
action. It is nonsingular for `μ ⊗ Leb`, with Radon–Nikodym derivative `RN_g(x)`, because
translations preserve `Leb`. The element `z` acts by `(x, t) ↦ (x, t + 1)`.

Let `π` be the Koopman representation of `G` on `L²(Ω)`, a unitary representation by (I3).

**Step 2 (coefficients).** For `L > 0` put `η_{n,L}(x, t) = ξ_n(x) · L^{-1/2} 1_{[0,L]}(t)`, a
unit vector. Write `b_g(x) = β(g, g^{-1}x)`. Then
`φ_{n,L}(g) := ⟨π(g)η_{n,L}, η_{n,L}⟩ = ∫_X ξ_n(x) ξ_n(g^{-1}x) RN_g(x)^{1/2} · (1 − |b_g(x)|/L)_+ dμ(x)`,
since `|[0,L] ∩ ([0,L] + b)| = (L − |b|)_+`.

The function `w_g = ξ_n · (κ(g)ξ_n) ≥ 0` is in `L¹` with `‖w_g‖_1 ≤ 1`, by Cauchy–Schwarz. It
dominates every integrand below.

**Step 3 (limits).**
- (a) As `L → ∞`, `φ_{n,L}(g) → ⟨κ(p(g))ξ_n, ξ_n⟩` by dominated convergence. The factor
  `(1 − |b_g|/L)_+` tends to `1` pointwise, since `b_g` is finite a.e.
- (b) Fix `n`, `L` and `g`. By Step 1, `RN_{gz^m} = RN_g` and `b_{gz^m} = b_g + m`. So
  `φ_{n,L}(g z^m) = ∫ w_g (1 − |b_g + m|/L)_+ dμ`, and this tends to `0` as `|m| → ∞` by dominated
  convergence (the integrand tends to `0` pointwise).

**Step 4 (C_0 functions).** By (I1) for `Q`, take normalized positive definite `C_0` functions
`θ_k` on `Q` with `θ_k → 1` pointwise. Put `Φ = φ_{n,L} · (θ_k ∘ p)`. It is positive definite
by (I2), and `Φ(e) = 1`.

`Φ` is `C_0`. Fix `ε > 0`. Since `|φ_{n,L}| ≤ 1`, the set `{|Φ| ≥ ε}` lies in `p^{-1}(F)` with
`F = {|θ_k| ≥ ε}` finite. That is a finite union of cosets `g_i⟨z⟩`, and by Step 3(b) each coset
meets `{|φ_{n,L}| ≥ ε}` in a finite set.

**Step 5 (diagonal).** Enumerate `G = {g_1, g_2, ...}`. For each `j`:
- choose `n` with `|⟨κ(p(g_i))ξ_n, ξ_n⟩ − 1| < 1/(3j)` for `i ≤ j` (hypothesis 2);
- then choose `L` by Step 3(a), and `k` by `θ_k → 1`, so that the resulting `Φ_j` satisfies
  `|Φ_j(g_i) − 1| < 1/j` for `i ≤ j`.

Then `Φ_j → 1` pointwise. By (I1), `G` has the Haagerup property. ∎

**Remark (why no integrability is needed).** The only use of `β` is through `b_g` being finite
a.e. and shifting by exactly `m` along cosets. Heavy tails of `β(g, ·)` are harmless here. They
are exactly what `perfect-extension-splittings-are-not-uniformly-integrable` forces when
`Hom(G, R)` vanishes on `z`.
