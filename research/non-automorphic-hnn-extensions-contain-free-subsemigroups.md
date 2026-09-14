---
rg: 2
id: non-automorphic-hnn-extensions-contain-free-subsemigroups
kind: claim
title: An HNN extension contains a free subsemigroup of rank two unless both associated subgroups equal the base
distinct_from:
  non-ascending-hnn-extensions-lack-bvc: that shows non-ascending HNN extensions lack property BVC; this shows every HNN extension other than a semidirect product with Z has a free subsemigroup, including ascending ones
  proper-self-conjugate-subgroups-force-free-subsemigroups: that works inside any group from a proper self-conjugate subgroup; this uses the HNN normal form and also covers non-ascending extensions
---

**Statement.** Let `G = HNN(H, K, L, psi) = <H, t | t k t^{-1} = psi(k), k in K>` with
`psi: K -> L` an isomorphism of subgroups of `H`.

1. If `K != H`, then for any `a in H \ K` the elements `t a` and `t` freely generate a free
   subsemigroup of rank 2.
2. If `L != H`, then for any `b in H \ L` the elements `t^{-1} b` and `t^{-1}` do.
3. So `G` has no free subsemigroup of rank 2 only if `K = L = H`, i.e. `psi` is an automorphism
   of `H` and `G = H ⋊_psi Z`.

Elementary; no novelty is claimed.
