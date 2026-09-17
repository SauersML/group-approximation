---
rg: 2
id: char-zero-upper-triangular-cloning-not-in-v-via-corwin
kind: route
title: "Z ≀ Z^2 sits inside T(B_*(R)) in characteristic 0, and Corwin's theorem forbids it in V"
target: char-zero-upper-triangular-cloning-groups-do-not-embed-in-v
requires:
  - upper-triangular-cloning-groups-contain-lamp-wreath-z2
  - wreath-z-by-z2-does-not-embed-in-thompson-v
---

Let `R` be a ring in which `Z → R` is injective. Then `(Z,+)` is a subgroup of `(R,+)`.

1. By `upper-triangular-cloning-groups-contain-lamp-wreath-z2`, the group `T(B_*(R))` contains
   `(R,+) ≀ Z^2`.
2. In `(R,+) ≀ Z^2 = (⊕_{Z^2} R) ⋊ Z^2`, the subgroup `(⊕_{Z^2} Z) ⋊ Z^2` is `Z^2`-invariant
   and is isomorphic to `Z ≀ Z^2`.
   - In the route `upper-triangular-cloning-lamp-wreath-proof` §5 this is the case `λ ∈ Z·1`:
     the lamps with integer coefficients, together with the same `g, h`.
3. So `Z ≀ Z^2` is a subgroup of `T(B_*(R))`.
4. Suppose `ι: T(B_*(R)) → V` is injective. Restricting `ι` to that subgroup embeds `Z ≀ Z^2` in
   `V`, which contradicts `wreath-z-by-z2-does-not-embed-in-thompson-v`.

Therefore `T(B_*(R))` does not embed in `V`. ∎
