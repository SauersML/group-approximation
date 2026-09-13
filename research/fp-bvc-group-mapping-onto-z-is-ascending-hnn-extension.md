---
rg: 2
id: fp-bvc-group-mapping-onto-z-is-ascending-hnn-extension
kind: claim
title: A finitely presented group with BVC mapping onto Z is an ascending HNN extension of an infinite finitely generated subgroup of the kernel, or is virtually cyclic
distinct_from:
  bieri-strebel-splitting-over-kernel-of-map-to-z: that claim splits every finitely presented group mapping onto Z; this claim adds BVC and concludes the splitting is ascending, with base infinite unless the group is virtually cyclic
---

**Statement.** Let `G` be finitely presented with property BVC, and `phi: G -> Z` surjective.
Then `G ≅ <H, t | t x t^{-1} = theta(x), x in H>` for a finitely generated subgroup
`H <= ker phi` and an injective endomorphism `theta: H -> H` (after replacing `t` by `t^{-1}`
if necessary), with `phi(t) = ±1` and

`ker phi = union over i >= 0 of t^{-i} H t^i`, an increasing union of copies of `H`.

Moreover:

- If `H` is finite, `G` is virtually cyclic.
- For `alpha` = conjugation by `t` on `ker phi`, `R(alpha^m) <= m·C` for all `m >= 1`
  (`bvc-bounds-conjugacy-classes-in-fibers-of-maps-to-z`).
- Since BVC passes to finite-index subgroups (von Puttkamer–Wu 1607.03790, Lemma 1.11), the
  same holds for any finite-index subgroup of `G` that maps onto `Z`.

**Consequence for the von Puttkamer–Wu conjecture.** A finitely presented, non-virtually-cyclic
group with BVC and positive virtual first Betti number has a finite-index subgroup that is an
ascending HNN extension of an infinite finitely generated group `H` along an injective
endomorphism, and that increasing union of copies of `H` is the kernel. The finite presentation
must be used beyond this: `osin-group-times-z-has-bvc` shows the kernel shape and bounded
Reidemeister numbers are compatible with BVC for finitely generated groups.
