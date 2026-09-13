---
rg: 2
id: fp-bvc-group-mapping-onto-z-is-ascending-hnn-extension-proof
kind: route
title: Bieri–Strebel splitting plus the non-ascending HNN obstruction
target: fp-bvc-group-mapping-onto-z-is-ascending-hnn-extension
requires:
  - bieri-strebel-splitting-over-kernel-of-map-to-z
  - non-ascending-hnn-extensions-lack-bvc
  - bvc-bounds-conjugacy-classes-in-fibers-of-maps-to-z
---

Let `G` be finitely presented with BVC and `phi: G -> Z` onto.

1. By `bieri-strebel-splitting-over-kernel-of-map-to-z`, `G = HNN(H, K, L, psi)` with `H`
   finitely generated, `H <= ker phi`, `psi: K -> L`, and `ker phi = <<H>>`.
2. By `non-ascending-hnn-extensions-lack-bvc`, `[H:K] >= 2` and `[H:L] >= 2` cannot both
   hold. So `K = H` or `L = H`. If `K = H`, put `theta = psi: H -> L <= H`. If `L = H`,
   replace the stable letter `t` by `t^{-1}` and put `theta = psi^{-1}: H -> K <= H`. Either
   way `theta` is an injective endomorphism of `H`, and
   `G = <H, t | t x t^{-1} = theta(x), x in H>`.
3. In an ascending HNN extension, `<<H>> = union over i >= 0 of t^{-i} H t^i`. This is von
   Puttkamer–Wu 1607.03790, Lemma 2.7, read on page 9. Directly: `t^{-i} H t^i` contains
   `t^{-(i-1)} theta(H) t^{i-1}`, and the union is normal because
   `t · t^{-i} H t^i · t^{-1} = t^{-(i-1)} H t^{i-1}` for `i >= 1`, while
   `t H t^{-1} = theta(H) <= H`. The union is increasing, and each member is isomorphic to
   `H` by conjugation.
4. If `H` is finite, the injective endomorphism `theta` of the finite group `H` is bijective.
   Then `t^{-i} H t^i = H` for all `i`, so `ker phi = H` is finite and `G = H ⋊ Z` is
   virtually cyclic.
5. The Reidemeister bound is the semidirect-product corollary of
   `bvc-bounds-conjugacy-classes-in-fibers-of-maps-to-z`, since `G = ker phi ⋊ <t>`.
