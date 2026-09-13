---
rg: 2
id: kun-thom-wreath-l2-acyclic-proof
kind: route
title: The lamp group is an infinite normal abelian subgroup
target: kun-thom-wreath-is-l2-acyclic
requires: [l2-betti-numbers-vanish-with-infinite-normal-amenable-subgroup]
---

- **The index `[G:Γ]` is infinite.** If `[G:Γ]` were finite, then `gΓg^(-1) <= Γ` with
  `[G:gΓg^(-1)] = [G:Γ]` would force `gΓg^(-1) = Γ`. So the compression semigroup `P_Γ` would
  be the normalizer of `Γ`, which generates `G` only if `Γ` is normal. Kun--Thom's `Γ` is
  infranormal and not normal.
- So `⊕_(G/Γ) Z/2` is infinite, abelian and normal in `W`. Cheeger--Gromov vanishing gives
  `β_n^(2)(W) = 0` for all `n`.
