---
rg: 2
id: nonhyperlinear-from-single-context-v4-exit-capacity
kind: route
title: An unconditional one-context V4 capacity cell directly gives a nonhyperlinear group
target: non-hyperlinear-group
requires:
  - same-context-s3-endpoint-atlas
  - single-context-v4-exit-capacity-is-already-nonhyperlinearity
---

This is a direct implication, not a modular simplification of the BCS
groupification problem.  The claim `same-context-s3-endpoint-atlas` asks for
a finitely presented extension containing an injective full-V4 packet, an
exact marked tracial model, and dimension-independent finite-matrix exit
estimates `(SCA1)--(SCA2)`.  Choose any one of its context cells.  Those are
exactly the hypotheses `(LCN1)--(LCN2)` of
`single-context-v4-exit-capacity-is-already-nonhyperlinearity` (with the
fixed-packet exactification loss absorbed into its modulus).  The canonical
regular trace assigns the parent packet projection a fixed positive
Plancherel mass, while the five-fourths surplus inequality forces that mass
to vanish along any normalized-HS microstate sequence.  Hence the constructed
group is nonhyperlinear.

This route is intentionally labeled **root-equivalent**: proving its open
prerequisite already constructs the desired group.  It does not reduce the
problem to a reusable local gadget, and it must not be substituted for the
genuinely global, cross-context target `globally-conditioned-v4-exit-capacity`.
