---
rg: 2
id: fw-nst-one-vertex-group-proof
kind: route
title: The coordinate kernels of the virtual embedding cannot all contain a power of the central generator
target: fw-nst-inputs-virtually-embed-in-one-vertex-group
requires:
  - fw-subgroups-of-eventually-similar-groups-virtually-embed
---

Notation as in the target.

**Step 1: the product embedding.** By part 1 of
`fw-subgroups-of-eventually-similar-groups-virtually-embed`, some finite-index
subgroup `K_0 <= K` has an injective homomorphism
`iota = (iota_1, ..., iota_m): K_0 -> H_(s_1) x ... x H_(s_m)`. Put
`N_i = ker(iota_i)`. Each `N_i` is normal in `K_0`, and the intersection of all
`N_i` is trivial.

**Step 2: a power of `z` in `K_0`.** Since `[K : K_0]` is finite, the cosets
`z^j K_0` cannot all be distinct, so `z^a` lies in `K_0` for some `a >= 1`.
Put `Z_0 = <z^a>`, an infinite cyclic subgroup of `K_0`.

**Step 3: finite-index kernels meet `Z_0`.** If `[K_0 : N_i]` is finite, then
`N_i cap Z_0` has index at most `[K_0 : N_i]` in `Z_0`, so it is nontrivial.

**Step 4: some kernel misses `Z_0`.** Suppose every `N_i cap Z_0` were
nontrivial, say equal to `<z^(a k_i)>` with `k_i >= 1`. With `k` the least
common multiple of the `k_i`, `z^(a k)` would lie in every `N_i`, hence in
their trivial intersection, contradicting that `z` has infinite order. So some
`i_0` has `N_(i_0) cap Z_0 = 1`.

**Step 5: that kernel is finite.** By step 3, `N_(i_0)` has infinite index in
`K_0`. By hypothesis (D) applied to `L = K_0` and `N = N_(i_0)`, the subgroup
`N_(i_0) cap Z` has finite index in `N_(i_0)`. It is a subgroup of the infinite
cyclic group `Z` meeting `Z_0` trivially. A nontrivial subgroup `<z^b>` of `Z`
meets `Z_0` in `<z^(lcm(a,b))> != 1`, so `N_(i_0) cap Z = 1`. So `N_(i_0)` is
finite.

**Step 6: conclusion.** Put `L = K_0`, `F = N_(i_0)` and `s = s_(i_0)`. The
coordinate `iota_(i_0)` factors through an injective homomorphism
`L / F -> H_s`. `F cap Z = 1` because `F` is finite and `Z` is torsion-free.
The image of `L cap Z`, which contains `z^a`, is central because `z` is central
in `K`, and it is infinite cyclic because `F cap Z = 1`.
