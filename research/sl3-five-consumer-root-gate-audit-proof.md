---
rg: 2
id: sl3-five-consumer-root-gate-audit-proof
kind: route
title: Collapse the five transfer consumers to the canonical-double soficity fork
target: sl3-projective-transfer-five-consumers-share-one-root-gate
requires:
  - exact-projective-codensity-has-a-uniform-trace-square-gap
  - projective-transfer-linear-bound-equals-no-ultraproduct-leak
  - canonical-free-double-escapes-uniform-exact-projective-folding
  - sl3-double-one-near-vertex-forces-joint-near-exactness
  - sofic-sl3-vertex-action-produces-two-outlier-double-models
---

Inspecting the five direct consumers of
`projective-trace-square-transfer-for-sl3-pair` shows that one route already
lands at `non-hyperlinear-group`; the other four first export the same
transfer estimate through reusable commutant, stable-letter, double-fold, or
filtered-return interfaces.  None replaces the transfer hypothesis by a
strictly weaker root-bearing hypothesis.  Hence their direct-consumer count
is reuse, not independent root cascade.

For the minimal canonical trace class, amalgam normal form gives

```text
w=i_0(h)i_1(h)^(-1) !=1 in D=A *_C A,
```

because `h notin C`.  If `D` is hyperlinear, its canonical microstates have
`tr(w)->0`; if it is nonhyperlinear, there is no canonical microstate
sequence.  Therefore the assertion that every such sequence has
`|tr(w)|->1` is equivalent, at existence level, to nonhyperlinearity of this
fixed `D`.  It is a sharper certificate shape but not a weaker existence
problem.

The established one-vertex anchor theorem shows that a correctable vertex
forces joint near-exactness and fold collapse.  Thus
`sl3-canonical-double-has-a-correctable-vertex` removes precisely the
simultaneous-two-outlier sector.  Conversely,
`sofic-sl3-vertex-action-produces-two-outlier-double-models` says that
soficity of `A` acting on `A/C` produces canonical double microstates in
that sector and refutes the correction statement.  This is the claimed
action-soficity fork.

Finally the exact projective gap and the ultraproduct linearization theorem
locate the universal statement correctly, while
`canonical-free-double-escapes-uniform-exact-projective-folding` rules out a
formal exact-to-canonical compactness promotion.  These facts prove all
three priority conclusions in the claim.

