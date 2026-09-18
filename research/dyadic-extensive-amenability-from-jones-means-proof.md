---
rg: 2
id: dyadic-extensive-amenability-from-jones-means-proof
kind: route
title: The digit-parity boundary cocycle of Jones' coset space has slope-parity point characters, so the twisted-lamplighter principle applies
target: dyadic-extensive-amenability-if-jones-subgroup-coamenable
requires: [jones-subgroup-is-stabilizer-of-odd-digit-sum-dyadics, twisted-lamplighter-point-character-gives-extensive-amenability]
artifacts:
  - experiments/jones-mean-collapse-2026-09-17/boundary_cocycle_check.py
---

**Conventions.** `F` is the group of orientation-preserving piecewise-linear homeomorphisms of `[0,1]`.
Each has finitely many breakpoints, all in `D`, and slopes in `2^ℤ`. On each piece it is
`t ↦ 2^b t + β` with `b ∈ ℤ` and `β ∈ ℤ[1/2]`, so `F` preserves `D = ℤ[1/2] ∩ (0,1)`. For `t ∈ D`, `n(t)`
is the exponent of its reduced denominator, i.e. its binary length. `P(t) ∈ ℤ/2` is the parity of its binary
digit sum, with `P(0) = 0`. `S = {t ∈ D : P(t) = 1}`. By `jones-subgroup-is-stabilizer-of-odd-digit-sum-dyadics`,
`\vec F = {g ∈ F : gS = S}`. So `gS ↦ g\vec F` is an `F`-equivariant bijection from the orbit `O = F·S` onto
`F/\vec F`, and an invariant mean on `F/\vec F` is the same as one on `O`.

**Lemma 1 (digit parity near a dyadic).** Let `x ∈ D` with `n = n(x)`, and let `s ∈ ℤ[1/2]` with
`0 < s < 2^(−n)` and `σ = 2^n s ∈ (0,1)`. Then
- (a) `P(x + s) = P(x) + P(σ)`;
- (b) `P(x − s) = P(x) + 1 + P(1 − σ)`;
- (c) `P(2^k σ) = P(σ)` whenever `2^k σ ∈ (0,1)`;
- (d) `P(1 − 2^k σ) = P(1 − σ) + k` whenever `2^k σ ∈ (0,1)`.

*Proof.* (a) The binary digits of `x` occupy positions `≤ n` and those of `s` positions `> n`, with no carry.
(b) `x − s = (x − 2^(−n)) + 2^(−n)(1 − σ)`. The first term is `x` with its last digit `1` (at position `n`)
cleared, so it has digit parity `P(x) + 1`; the second occupies positions `> n`. (c) Shifting does not change
digits. (d) For `σ < 1/2`, `1 − σ ∈ (1/2, 1)` has expansion `.1u` with `u` nonempty, and
`1 − 2σ = 2(1 − σ) − 1 = .u`, so `P(1 − 2σ) = P(1 − σ) + 1`. Induction gives `k ≥ 0`. Negative `k` follows by
applying the positive case to `2^k σ`. ∎

**Lemma 2 (the sets `Z_h`).** For `h ∈ F` let `Z_h = {t ∈ D : P(ht) ≠ P(t)} = h⁻¹S Δ S`. Fix `x ∈ D`, let
`y = hx`, `m = n(y)`, `n = n(x)`, and let `2^b = h'(x⁻)`, `2^(b')= h'(x⁺)`. For all sufficiently small
dyadic `s > 0`:
- `[x + s ∈ Z_h] = [x ∈ Z_h] = P(y) − P(x)`;
- `[x − s ∈ Z_h] = P(y) − P(x) + m + b − n`.

*Proof.* For small `s`, `h(x ± s)` is `y + 2^(b')s` or `y − 2^b s`, and `s`, `2^b s`, `2^(b')s` are below
`2^(−n)` and `2^(−m)`. By Lemma 1(a),(c),
`P(y + 2^(b')s) − P(x + s) = P(y) + P(2^(m+b')s) − P(x) − P(2^n s) = P(y) − P(x)`. By Lemma 1(b),(d),
`P(y − 2^b s) − P(x − s) = P(y) + P(1 − 2^(m+b−n)σ) − P(x) − P(1 − σ) = P(y) − P(x) + m + b − n`, with
`σ = 2^n s`. ∎

**Boundaries.** Let `𝒵` be the class of `Z ⊆ D` such that at every `x ∈ D` the indicator of `Z` is constant on
`(x − ε, x) ∩ D` for some `ε > 0`, with value `Z(x⁻)`. For `Z ∈ 𝒵` set
`∂Z = {x ∈ D : [x ∈ Z] ≠ Z(x⁻)}`. Then:
- `𝒵` is closed under `Δ`, and `∂(Z Δ Z') = ∂Z Δ ∂Z'`, since germs add mod 2.
- `g𝒵 = 𝒵` and `∂(gZ) = g∂Z` for `g ∈ F`: `g` is an increasing bijection of `D` carrying
  `(x − ε, x) ∩ D` onto a left neighbourhood of `gx` in `D`.
- By Lemma 2, `Z_h ∈ 𝒵`, and `x ∈ ∂Z_h` iff `n(hx) − n(x) + log₂ h'(x⁻)` is odd.

**Lemma 3 (`∂Z_h` is finite).** Take a piece `(p, q]` of `h` on which `h(t) = 2^b t + β`, with `β` of
denominator `2^(n(β))` (`n(β) = 0` if `β ∈ ℤ`). If `x ∈ (p, q] ∩ D` has `n(x) − b > n(β)`, then
`2^b x = odd/2^(n(x)−b)` and `β` has smaller denominator. So `n(hx) = n(x) − b`, and since `h'(x⁻) = 2^b`
the parity `n(hx) − n(x) + b` is `0`. Hence `∂Z_h ∩ (p, q]` lies among the finitely many dyadics of length
`≤ n(β) + b`. There are finitely many pieces, and `(0, 1] ∩ D` is covered. ∎

**The twisted model.** For `Y ∈ O`, say `Y = kS`, we have `Y Δ S = Z_(k⁻¹) ∈ 𝒵`. Define
`Φ(Y) = ∂(Y Δ S) ∈ P_f(D)` and `c(g) = Φ(gS) = ∂Z_(g⁻¹)`. Since `gY Δ S = g(Y Δ S) Δ (gS Δ S)`,
`Φ(gY) = gΦ(Y) Δ c(g)`. Applied to `Y = kS` this gives the cocycle identity `c(gk) = g·c(k) Δ c(g)`. With
`A = ℤ/2` and `P_f(D) ≅ (ℤ/2)^(D)`, `c` is a 1-cocycle as in
`twisted-lamplighter-point-character-gives-extensive-amenability`, and `Φ: O → P_f(D)` is equivariant from
`F ↷ O` to `⋆`.

**Nontrivial point characters.** Fix `x ∈ D`. Let `d = 2^(−(n(x)+3))`, so `x − 4d > 0`. Define `h` to be the
identity on `[0, x − 4d] ∪ [x, 1]`, affine from `[x − 4d, x − 2d]` onto `[x − 4d, x − 3d]` (slope `1/2`), from
`[x − 2d, x − d]` onto `[x − 3d, x − 2d]` (slope `1`), and from `[x − d, x]` onto `[x − 2d, x]` (slope `2`).
Its breakpoints are dyadic, its slopes are powers of 2 and it is an increasing homeomorphism, so `h ∈ F_x`
with `h'(x⁻) = 2`. Let `g = h⁻¹ ∈ F_x`. Then `c(g) = ∂Z_h`, and `n(hx) − n(x) + 1 = 1` is odd, so
`ψ_x(g) = [x ∈ c(g)] = 1 ≠ 0`. (More generally, `ψ_x(g)` is the parity of `log₂ g'(x⁻)`.)

**Conclusion.** Let `m` be an `F`-invariant mean on `F/\vec F`, hence on `O`. Its pushforward `Φ_* m` is a
`⋆`-invariant mean on `P_f(D)`. Every point character is nontrivial, so
`twisted-lamplighter-point-character-gives-extensive-amenability` gives extensive amenability of `F ↷ D`. ∎

**Checks.** The artifact script checks Lemma 2's germ formula on random words in `x₀, x₁`, together with
finiteness, the cocycle identity, `c(x₀) = {1/2}`, `c(x₁) = {3/4}` (consistent with item 3 of
`jones-subgroup-cosets-form-a-parity-lamplighter`), and the point-character element above.
