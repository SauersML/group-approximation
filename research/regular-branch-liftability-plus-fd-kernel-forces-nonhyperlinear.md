---
rg: 2
id: regular-branch-liftability-plus-fd-kernel-forces-nonhyperlinear
kind: claim
title: Correcting only canonical regular microstates already detects a finite-dimensional residual kernel
distinct_from:
  hs-stability-plus-fd-residual-forces-nonhyperlinearity: that assumes flexible HS stability for every approximate representation; this needs correction only on the canonical regular-trace branch supplied by hyperlinearity.
  hyperlinear-hs-stable-is-residually-finite: that derives residual finiteness from full same-profile stability; this retains only one marked word killed by every finite-dimensional representation.
---

Let `Gamma=<S|R>` be finitely generated and let `w!=1`.  Assume every
canonical regular-trace normalized-HS microstate sequence for `Gamma` can,
after a relative dimension change tending to zero, be corrected on `S` to
genuine finite-dimensional unitary representations.  If every such genuine
representation sends `w` to the identity, then `Gamma` is nonhyperlinear.

Thus full HS stability is stronger than the terminal input.  It is enough to
correct the one trace profile that hyperlinearity itself supplies.  This does
not follow from separately exactifying finite subgroups: their overlap
identifications retain multiplicity-commutant holonomy.

