---
rg: 2
id: nonsofic-hyperbolic-group-from-titz-witzel-flat-hitting-covers
kind: route
title: A nonsofic Titz--Witzel kernel plus flat-hitting sparse branched covers yields a nonsofic hyperbolic group
target: nonsofic-hyperbolic-group
requires:
  - titz-witzel-kernel-nonsofic
  - titz-witzel-flat-hitting-sparse-branched-covers
  - flat-hitting-branched-covers-have-hyperbolic-pi1
  - sparse-branched-covers-with-sofic-pi1-give-sofic-lattice
  - sofic-kernel-amenable-quotient-permanence
---

**OPEN.**

1. Suppose the simple kernel is nonsofic.  It has index two in
   `G = pi_1(Y_1^2)`, so `G` is nonsofic: by permanence, sofic `G` would
   make the kernel sofic.
2. Let `X_k` be the covers of `titz-witzel-flat-hitting-sparse-branched-covers`,
   with `beta(X_k) -> 0`, (G) and (H).
3. If all but finitely many `pi_1(X_k)` were sofic, part 1 of
   `sparse-branched-covers-with-sofic-pi1-give-sofic-lattice` would make `G`
   sofic.  So some `pi_1(X_k)` is nonsofic.
4. It is hyperbolic by `flat-hitting-branched-covers-have-hyperbolic-pi1`.

This is distinct from `cocycle-stability-nonsofic-route`, which uses random
Linial--Meshulam complexes and a coding-theoretic stability rate.  Here the
nonsoficity mechanism would be supplied by one explicit simple Kazhdan
lattice, and hyperbolization is a finite combinatorial condition on branch
sets.

The route also shows that a nonsoficity proof for the kernel cannot be
purely local and geometric unless it breaks at (H).  Such a proof would
otherwise settle the nonsofic hyperbolic group problem.
