---
rg: 2
id: sl2-root-kazhdan-triangle-untwisted-member-maps-onto-sl2-proof
kind: route
title: Conjugating the two SL_2(q) vertices by h and h u(1/P), with P^2 = 1/s, matches all three edge parametrizations
target: sl2-root-kazhdan-triangle-untwisted-member-maps-onto-sl2
requires: [triangle-of-groups-half-girth-structure]
---

All computations are in characteristic 2, so `-1 = 1` and `u(x)^{-1} = u(x)`.

**The inverse of h.** `h^{-1} = [[0, 1], [1, P]]`, because `[[P,1],[1,0]]·[[0,1],[1,P]] = [[1, P+P],[0,1]] = I`.

**Edge `E_13`.** `h^{-1} u(x) h = [[0,1],[1,x+P]]·[[P,1],[1,0]] = [[1,0],[x,1]] = v(x)`. Hence
`ρ_1(v(x)) = h v(x) h^{-1} = u(x) = ρ_3(u(x))`, which is the gluing `E_13 ∋ x ↦ u(x)` at `A_3`.

**Edge `E_12`.** `h' = h u(1/P)`, and `u(1/P)` commutes with `u(x)`. So
`ρ_2(u(x)) = h u(1/P) u(x) u(1/P) h^{-1} = h u(x) h^{-1} = ρ_1(u(x))`.

**Edge `E_23`.** For a lower triangular `[[a,0],[c,d]]`,

```text
[[a,0],[c,d]] · v(y) · [[a,0],[c,d]]^{-1}  =  [[a,0],[c+dy,d]] · [[1/a,0],[-c/(ad),1/d]]  =  v(dy/a).
```

For `h' = [[P,0],[1,1/P]]` this gives `ρ_2(v(x)) = v(x/P^2) = v(sx) = ρ_3` applied to the gluing
`E_23 ∋ x ↦ v(sx)` at `A_3`.

**Conclusion.** The three restrictions agree on each edge group under the given parametrizations. By the
universal property of the colimit they define `ρ: Λ_0 -> SL_2(F)`.
- Each `ρ_i` is a conjugation or the identity, so `ρ` is injective on each vertex group.
- `ρ(A_3) = SL_2(F)`, so `ρ` is onto.
- The vertex groups `A_i` are the vertex stabilizers of the development
  (`triangle-of-groups-half-girth-structure` (i)). By (iv) of that claim, `ker ρ` is torsion-free.

**Absorbing a scalar twist on `E_23`.** Replacing `x ↦ v(sx)` by `x ↦ v(sλ^{-1}x)` with `λ ∈ k^*` is
handled by `P = (λ/s)^{1/2}`. Then `h' v(x) h'^{-1} = v(x/P^2) = v(sλ^{-1}x)`, and the other two edges are
unchanged. ∎
