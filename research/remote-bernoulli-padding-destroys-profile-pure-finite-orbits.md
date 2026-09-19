---
rg: 2
id: remote-bernoulli-padding-destroys-profile-pure-finite-orbits
kind: claim
title: Remote Bernoulli padding destroys every profile-pure finite projection orbit without changing a perfect ZPC gap
distinct_from:
  finite-depth-readable-groupoid-closes-iff-full-orbit-is-finite: that shows the full readable translate algebra can grow forever in a standalone always-accept ZPC model; this rules out even one finite-orbit projection below a readable profile and preserves an arbitrary strict-gap game by padding.
  bcv-halt-readable-finite-orbit-does-not-transfer-to-gap-irs: that separates the HALT completeness strategy from the NONHALT compactness witness; this gives a direct computable padding operation showing why compactness, ergodicity, and finite verifier state cannot force the weaker profile-pure orbit either.
  perfect-gap-zpc-has-profile-pure-finite-projection-orbit: that asks for the existence of one specially chosen witness with such an orbit; this proves the property is not forced by the formal ZPC gap axioms and is not weak-star closed, but does not exclude a source-specific unpadded witness.
---

Let `G` be any finite tailored game with a perfect ZPC-IRS strategy and
`omega*(G)<1`. There is a finite always-accept remote padding producing a
game `G^B` such that

```text
omega_ZIRS(G^B)=1,
omega*(G^B)<1,                                           (RBP1)
```

and `G^B` has a perfect ZPC-IRS strategy in which no nonzero projection below
one full readable profile has a finite conjugacy orbit under the structural
unreadable group.

The padding may be made ergodic whenever the original witness is replaced by
an ergodic component. The standalone always-accept Bernoulli padding factor
is a fixed-cylinder limit of finite cyclic padding factors with finite
readable orbit, so finite-orbit structure is not weak-star closed even in
that elementary ZPC class. No claim is made that tensoring those cyclic
factors with an arbitrary original witness gives the total product a finite
orbit. Consequently a profile-pure finite projection orbit is neither a
formal consequence of perfect ZPC plus a strict quantum gap nor something
that fixed-cylinder compactness can preserve without an additional uniform
source bound.
