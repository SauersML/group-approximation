---
rg: 2
id: fp-subshift-full-group-subgroups-extend-to-sft-proof
kind: route
title: Formal-cocycle SFT conditions carry the relators off the subshift
target: fp-subshift-full-group-subgroups-extend-to-sft
requires: []
artifacts:
  - research/artifacts/fp-simple-amenable-full-groups-2026-09-12.md
---

## Why sufficient

1. **Local rules.** On a free subshift, each element of `[[Lambda ~ X]]` has a
   unique continuous cocycle, which is locally constant. So it is `T_c` for a
   local rule `c: A^D -> Lambda`, where `T_c(x) = c(x|_D) . x`.
2. **Formal cocycles.** Compositions of local rules are local rules. The formal
   cocycle of a word depends on `x` only on a finite window.
3. **Inverses.** Let `Y_2` be the set of `x` where, at every translate, the formal
   cocycles of `s_i^{-1} s_i` and `s_i s_i^{-1}` are `e`. It is an SFT, and it
   contains `X`, because those words act trivially there and the action is free.
   On `Y_2` the maps `T_{c_i}` and `T_{c_i'}` are inverse, orbit-preserving
   homeomorphisms.
4. **Relators.** Let `Y ⊆ Y_2` add the conditions that the formal cocycle of each
   relator `r_j` is `e` at every translate. `Y` is an SFT containing `X`, and
   each `r_j(hat g)` is the identity on `Y`.
5. **Isomorphism.** `pi: Gamma -> Delta_Y`, `s_i -> hat g_i|_Y`, is a surjective
   homomorphism, and restriction `rho: Delta_Y -> Gamma` satisfies `rho pi = id`.
   So `pi` is an isomorphism.
6. **Simple case.** The kernel of `Gamma -> Homeo(Z)` is normal, so it is trivial
   or `Gamma`. A finite `Z` has a finite image, which an infinite `Gamma` can
   only map onto trivially.
