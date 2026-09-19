---
rg: 2
id: houghton-groups-embed-in-thompson-v-proof
kind: route
title: Code each ray point (i,k) as the cone c_i 1^k 0, so that eventual translations become prefix replacements on the tails c_i 1^K
target: houghton-groups-embed-in-thompson-v
requires:
  - thompson-v-finitely-presented-infinite-simple
---

`V` is the group of homeomorphisms of `2^N` that map the cones of one complete prefix code
bijectively onto the cones of another by prefix replacement.

1. **Cells.**
   - Fix a complete prefix code `c_1, ..., c_n`: `c_i = 1^(i-1)0` for `i < n` and
     `c_n = 1^(n-1)`, or `c_1 = ∅` if `n = 1`.
   - Put `U(i,k) = c_i 1^k 0 2^N`. The cells `U(x)`, `x ∈ X`, are pairwise disjoint.
   - Their union is `2^N \ {c_i 1^∞ : i}`.
2. **The map.** For `h ∈ H_n` let `ι(h)` send `c_i 1^k 0 η ↦ c_j 1^l 0 η` whenever
   `h(i,k) = (j,l)`, and fix the `n` points `c_i 1^∞`.
3. **`ι(h) ∈ V`.**
   - Choose `K` as in the definition, with `K + m_i >= 0` for every `i`. Let
     `D = {(i,k) : k < K}`.
   - On the cone `c_i 1^K`, `ι(h)(c_i 1^K ζ) = c_i 1^{K+m_i} ζ` for every `ζ`: for `ζ = 1^j 0 η`
     this is the translation `(i, K+j) ↦ (i, K+j+m_i)`, and `ζ = 1^∞` is fixed.
   - So `ι(h)` is the prefix replacement taking the complete prefix code
     `{c_i 1^k 0 : (i,k) ∈ D} ∪ {c_i 1^K : i}` to `{cells of h(D)} ∪ {c_i 1^{K+m_i} : i}`.
   - The second family is also a complete prefix code. `h` is a bijection of `X`, so
     `X = h(D) ⊔ {(i,l) : l >= K + m_i}`. Hence the cells of `h(D)`, together with the cones
     `c_i 1^{K+m_i}` (which contain the remaining cells and the points `c_i 1^∞`), partition `2^N`.
4. **Homomorphism and injectivity.**
   - `ι(gh)` and `ι(g)ι(h)` agree on every cell, since both act there as `gh` acts on `X`. Both fix
     every point `c_i 1^∞`. So `ι` is a homomorphism.
   - It is injective because the cells are nonempty.

So `H_n ≤ V`. With `thompson-v-finitely-presented-infinite-simple`, every subgroup of `H_n`
embeds in a finitely presented simple group. ∎
