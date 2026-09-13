---
rg: 2
id: commuting-living-generators-give-sigma-one-proof
kind: route
title: Lift a Cayley path by powers of commuting living generators to stay in the half-space
target: commuting-living-generators-give-sigma-one
requires: []
---

**Definition used.** `Cay = Cay(Γ, S)` with edges `γ — γs` for `s in S^{±1}`. Let
`Cay_{χ>=0}` be the full subgraph on `{γ : χ(γ) >= 0}`. By Bieri–Neumann–Strebel,
`[χ] in Σ^1(Γ)` exactly when `Cay_{χ>=0}` is connected. This does not depend on the
finite generating set.

**Setup.** For `v in L` put `v' = v` if `χ(v) > 0` and `v' = v^{-1}` if `χ(v) < 0`, and
`L' = {v' : v in L}`. Then `L' ⊆ S^{±1}`, its elements pairwise commute, and
`c := min_{v' in L'} χ(v') > 0`. Hypothesis 2 holds with `L'` in place of `L`, since
commuting with `v` is the same as commuting with `v^{-1}`.

**Proof.** Take `γ, γ' in Cay_{χ>=0}` and any edge path
`γ = δ_0, δ_1 = δ_0 s_1, ..., δ_n = δ_{n-1} s_n = γ'` in `Cay` with `s_i in S^{±1}`. For each
`i`, choose `v_i in L'` commuting with `s_i` (hypothesis 2). Put
`μ = min_i χ(δ_i)` and choose an integer `N >= 0` with `μ + N c >= 0`. Build a new path
from four kinds of segments.

1. **Ascent.** `γ, γ v_1, ..., γ v_1^N`. The values `χ(γ) + j χ(v_1)` are `>= χ(γ) >= 0`.
2. **Lifted edges.** Since `s_i` commutes with `v_i`, the vertex `δ_{i-1} v_i^N` is joined to
   `δ_{i-1} v_i^N s_i = δ_{i-1} s_i v_i^N = δ_i v_i^N` by one `s_i`-edge. Both endpoints have
   `χ >= μ + N c >= 0`.
3. **Joints.** At `δ_i` with `1 <= i <= n-1`, go from `δ_i v_i^N` to `δ_i v_{i+1}^N` through
   `δ_i v_i^N v_{i+1}^j` for `j = 0..N`. Since `v_i` and `v_{i+1}` commute,
   `δ_i v_i^N v_{i+1}^N = δ_i v_{i+1}^N v_i^N`. Continue through `δ_i v_{i+1}^N v_i^j` for
   `j = N..0`. Every vertex has `χ >= χ(δ_i) + N c >= 0`.
4. **Descent.** `γ' v_n^N, γ' v_n^{N-1}, ..., γ'`. The values `χ(γ') + j χ(v_n)` are
   `>= χ(γ') >= 0`.

Every vertex of the concatenated path lies in `Cay_{χ>=0}`, so `γ` and `γ'` are joined in
`Cay_{χ>=0}`. Hence `Cay_{χ>=0}` is connected and `[χ] in Σ^1(Γ)`. ∎

**Model test.** Take `Γ = Z^2 = <a, b>` with `χ(a) = 1`, `χ(b) = 0`. Then `L = {a}`, and `b`
commutes with `a`. The lemma gives `[χ] in Σ^1(Z^2)`, which is correct. For `Γ = F_2` with the
same `χ`, hypothesis 2 fails (`b` commutes with no living generator), and indeed
`Σ^1(F_2) = ∅`.
