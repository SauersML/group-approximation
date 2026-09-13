---
rg: 2
id: heisenberg-in-nv-forces-drift-free-central-element-proof
kind: route
title: Integrate the offset cocycle against an invariant measure; distorted elements have zero drift
target: heisenberg-in-nv-forces-drift-free-central-element
requires: []
---

**Well-definedness and the cocycle identity.** If the rectangle piece containing
`p` is refined by appending a word `z_i` to `u_i`, the image prefix becomes
`v_i z_i`. So `|v_i| − |u_i|` is unchanged, and `s_g` depends only on `g` and
`p`. It is constant on the finitely many pieces, hence Borel and bounded.

For `gh` at `p`: refine the piece of `h` at `p` so that its image prefixes `v_i`
are at least as long as the domain prefixes `u'_i` of the piece of `g` at `h(p)`.
Then `g(v_iw) = v''_iw` with `|v''_i| − |v_i| = s_g(h(p))_i`, and
`gh(u_iw) = v''_iw`. So `s_{gh}(p) = s_g(h(p)) + s_h(p)`.

It follows that `s_{g^-1}(p) = −s_g(g^-1(p))`, and that for any word
`σ_1⋯σ_m` with `σ_j ∈ S ∪ S^-1`,
`|s_{σ_1⋯σ_m}(p)|_∞ <= mK`, using `sup|s_{σ^-1}| = sup|s_σ|`. So
`sup_p |s_h(p)|_∞ <= K|h|_S` for every `h ∈ ⟨S⟩`.

**Item 1.** Let `μ` be `g`-invariant. By the cocycle identity,
`s_{g^N} = Σ_{j=0}^{N−1} s_g ∘ g^j`, and invariance gives
`∫ s_{g^N} dμ = N ρ_μ(g)`. Hence
`N|ρ_μ(g)|_∞ <= sup_p |s_{g^N}(p)|_∞ <= K|g^N|_S`.

**Item 2.** From `ab = cba` and centrality, `a b^m = c^m b^m a`, and then
`a^m b^m = c^{m^2} b^m a^m`. So `c^{m^2} = [a^m, b^m]`, and with `S = {a, b}`,
`|c^{m^2}|_S <= 4m`. If `ρ_μ(c) ≠ 0` for some `c`-invariant `μ`, item 1 gives
`m^2 |ρ_μ(c)|_∞ <= 4mK` for every `m`, which is impossible.

**Item 3.** `x^{k^j} = t^j x t^-j`, so with `S = {x, t}`,
`|x^{k^j}|_S <= 2j + 1`. Item 1 gives `|k|^j |ρ_μ(x)|_∞ <= K(2j+1)` for every
`j`, which is impossible if `ρ_μ(x) ≠ 0`.

**Item 4.**
- `H_3(Z)`: its central generator `c = [a,b]` has infinite order and commutes
  with `a` and `b`, so it is drift-free by item 2. That contradicts the
  hypothesis.
- `BS(1,k)`: in `Z[1/k] ⋊ Z` the element `x` has infinite order. Item 3 gives
  the contradiction.
- `SL_d(Z)` with `d >= 3`: it contains `H_3(Z)` as the upper unitriangular
  matrices in the top-left `3 × 3` block, with `a = E_{12}`, `b = E_{23}` and
  `c = [a, b] = E_{13}` central and of infinite order.
- `GL_d(Z)` with `d >= 3`: it contains `SL_d(Z)`. ∎

Invariant measures exist for every `g`, since `C^n` is compact metrizable
(Krylov–Bogolyubov). So "drift-free" is never vacuous.
