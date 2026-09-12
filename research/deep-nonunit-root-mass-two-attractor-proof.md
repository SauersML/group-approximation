---
rg: 2
id: deep-nonunit-root-mass-two-attractor-proof
kind: route
title: Unit scaling bounds transported shapes from below, and two compressors with different Perron attractors cannot both carry deep mass
target: vertex-rounding-deep-nonunit-root-mass-vanishes
requires:
  - compressor-transport-exactifies-under-vertex-rounding
  - unit-type-vertex-rounding-forces-compressor-commutant-rigidity
  - vertex-rounding-non-unit-mass-at-origin
  - nonunit-component-root-mass-is-log-scale-folner
artifacts:
  - research/artifacts/nh-deep-mass-2026-09-12.md
---

Full derivation in the artifact, §§1–5.

**Shapes.** For an origin character `χ_0 = ψ ∘ λ_0`, let `Sh(χ_0) = {a : λ_0(x^a R_+) ≠ 0}`. It is finite and down-closed, with
`depth_nu = 1 + max{c : c·1 ∈ Sh}` and extents `e_i = max{c : c e_i ∈ Sh}`. By item 1 of the third premise, characters
at intermediate places carry vanishing mass. Transport acts componentwise: `(D_M χ)_0 = D_M χ_0`.

**Lemma 1, unit scaling.** By item 1 of the second premise, `π_n` factors through `St_r(B_n)`. There `h_31(u)`
conjugates `x_12(f)` to `x_12(u^(±1) f)`, so `μ_n` is invariant under `χ -> χ(u ·)` for `u ∈ B_n^×`. Hence `μ_n` is an
average of uniform measures on orbits of the origin units `A_0^×`, and `Sh` is constant on each orbit.

**Lemma 2, shape transport.** Let `M` be nonnegative and `w ∈ N^d ∖ 0`.
- (a) If `c w ∈ Sh(D_M χ_0)`, then `c M w ∈ Sh(χ_0)`.
- (b) Put `ℓ = max{j : (c+j) M w ∈ Sh(χ_0)}`. For `u` uniform in `A_0^×`, `P(c w ∉ Sh(D_M χ_0(u ·))) <= 2 q^(-(ℓ+1))`.

The event is `u ∈ ker Λ` for a linear `Λ`. The functionals `u -> λ_0(u x^(cMw) y^j)`, `y = x^(Mw)`, `j <= ℓ`, are
independent: a relation puts `x^(cMw) y^(j_0)·unit` in `J(χ_0)`, because `R_+/J(χ_0)` is local and `y` is nilpotent there.

**Lemma 3, Perron sandwich.** For `A` with every entry `>= 1`, `A^k e_i` lies within the factor `1 ± γ_k` of
`ℓ_i λ^k v`, with `γ_k -> 0`. So `max{c : c A^k e_i ∈ Sh}` is `s/(ℓ_i λ^k)` up to the factor `1 ± γ_k` and an additive `1`,
where `s = sup{t : ⌊t v⌋ ∈ Sh} >= depth`.

**Two attractors.**
- **Choice.** Take `A = (min(i,j))` and `B = P A P^(-1)`, with `P` the reversal permutation. Then
  `ℓ_(A,d) > ℓ_(A,1)`, and `ℓ_B = P ℓ_A`.
- **Concentration.** By Lemmas 2 and 3, apart from orbit probability `6 q^(-(L+1))`, `D_(A^k)` sends a character of
  depth `>= K` into `E_+ = {depth >= K', log(e_1/e_d) > β/2}`. `D_(B^k)` sends it into `E_- = {depth >= K', log(e_1/e_d) < -β/2}`.
- **Counting.** The first premise, applied to the compressors `A^k` and `B^k`, gives
  `μ_n(E_±) >= μ_n(depth >= K) - 6 q^(-(L+1)) - η_n^±`. Since `E_+`, `E_-` are disjoint inside `{depth >= K'}`:

  ```text
  μ_n(depth_nu > 1)  <=  ν_n + 2 μ_n(1 < depth_nu < K) + 12 q^(-(L+1)) + η_n^+ + η_n^-.
  ```

- **Conclusion.** Item 3 of the fourth premise gives `μ_n(1 < depth_nu < K) <= ⌈log_d K⌉ η_n`. Every term except
  `12 q^(-(L+1))` vanishes along `U`, and `L` is arbitrary.
