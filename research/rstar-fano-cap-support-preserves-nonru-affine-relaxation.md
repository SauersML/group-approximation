---
rg: 2
id: rstar-fano-cap-support-preserves-nonru-affine-relaxation
kind: claim
title: Fano-cap tracial supports preserve non-RU soundness under affine relaxation
distinct_from:
  tracial-support-affine-linearization: that proves perfect tracial completeness for every affine-support relaxation but does not preserve the original nonlinear predicate; this uses the one-ghost geometry to prove precisely that preservation.
  bcs-to-lcs-exact-support-gap: that asks for the existence of a suitable trace/support menu for a fixed non-RU BCS; this is the complete conditional theorem once all local supports of one trace are Fano caps.
---

ESTABLISHED.
Let `B` be a finite BCS all of whose nonlinear context predicates are copies
of the one-ghost relation `R_*`.  Suppose `B` has a tracial satisfying state
`tau` but no Connes-embeddable satisfying trace.  For every context let
`S_c` be the joint spectral support of `tau`.  If every translated support
`S_c+g` is a Fano cap, then the affine-support LCS `L_tau` is perfectly
tracially satisfiable and has no Connes-embeddable satisfying trace.

Indeed, perfect tracial completeness is the general affine-support theorem.
By `rstar-fano-ghost-affine-hull-criterion`, every affine hull
`Aff(S_c)` remains inside `R_*`.  Hence any trace satisfying `L_tau` also
satisfies every original `R_*` predicate and the unchanged overlap rows, and
therefore induces a trace satisfying `B`.  This implication holds equally
for a Connes-embeddable trace, contradicting the hypothesis on `B`.

Thus one Fano-cap support profile closes the exact BCS-to-LCS gap for that
instance.  The remaining uniform-machine issue is not the Kleene
orientation; it is selecting/authenticating one such profile in a finite
compiler before knowing which perfect model exists.
