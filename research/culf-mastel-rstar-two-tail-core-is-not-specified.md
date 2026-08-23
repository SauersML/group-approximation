---
rg: 2
id: culf-mastel-rstar-two-tail-core-is-not-specified
kind: claim
title: The published Culf--Mastel theorem does not specify a canonical R-star pp core
distinct_from:
  culf-mastel-rstar-reduction-is-support-blind: that records the absence of a support theorem; this records the more basic absence of concrete target gadget incidence data needed to compute a two-tail kernel.
  rstar-two-tail-peeling-reduces-fc-char-to-a-dense-kernel: that gives an effective reduction once an explicit finite R-star instance is supplied; this explains why the theorem statement alone does not yield the kernel.
---

**ESTABLISHED.**  Culf--Mastel Theorem 6.8 does not
fix an explicit pp reduction from each constant source relation to `R_*`.
Its proof invokes NP-completeness to assert a BCS `B'` satisfying Corollary
6.7, with each `D_i` the Boolean form of a `CSP(R_*)` instance.  Corollary
6.7 specifies the visible-extension property and separation of auxiliary
sets belonging to different source contexts, but it gives no list of target
rows or internal variable incidences inside a `D_i`.

The present repository likewise records the theorem-level specialization
and its consequences, but contains no serialized machine-indexed `R_*`
instance generator or concrete family of pp gadgets chosen in Theorem 6.8.
Therefore there is no canonical incidence kernel to compute from the cited
construction.  Given any explicit choice of the constant pp gadgets and any
finite source instance, the pinned or global two-tail kernel is computable by
the elementary deletion algorithm in
`rstar-two-tail-peeling-reduces-fc-char-to-a-dense-kernel`.

This is not merely missing exposition that could harmlessly be filled with
an acyclic gadget.  By
`nonaffine-source-gadgets-force-a-pinned-two-tail-kernel`, every exact pp
gadget for a nonaffine source relation necessarily leaves a nonempty pinned
kernel.  A proof of FC-char must choose concrete gadgets and solve their
finite cap-profile problem on those kernels, or use source-specific support
smaller than the full nonaffine relation.

One later incidence contribution *is* explicit and harmless:
`culf-mastel-rstar-commutativity-replacement-rows-peel-off` proves that every
Proposition 6.2 row used to replace an empty constraint has exactly two fresh
coordinates and disappears under two-tail peeling.  What remains unspecified
is precisely the dense part of the NP pp gadgets.

Primary source: Culf--Mastel, arXiv:2410.21223v2, Corollary 6.7 and Theorem
6.8, especially the NP-completeness invocation in the first sentence of the
second paragraph of the proof of Theorem 6.8.
