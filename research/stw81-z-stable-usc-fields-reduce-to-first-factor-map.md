---
rg: 2
id: stw81-z-stable-usc-fields-reduce-to-first-factor-map
kind: claim
title: The stably finite field seam is exactly the nonsimple Z first-factor map problem
distinct_from:
  stw81-finite-base-usc-fibre-product-bound: that theorem gives the base-times-fibre estimate for arbitrary finite-dimensional fibres; the present result globalizes Z-stability and identifies the exact map whose colour count must drop.
  stw81-fibrewise-oinfinity-absorption-collapses-base-colours: O-infinity-stability has a nonsimple nuclear-dimension-one theorem after globalization; no corresponding theorem is known for nonsimple Z-stable algebras, and the constant Z-field already exposes the gap.
  stw81-connected-base-blocks-clopen-colour-reuse: that is a topological obstruction to clopen finite-stage approximation; the present firewall survives even for the globally trivial field C([0,1]) tensor Z and is an analytic order-zero-map problem.
artifacts:
  - research/artifacts/stw81-z-stable-field-first-factor-firewall-2026-08-30.md
---

Let `X` be a finite-dimensional second-countable locally compact Hausdorff
space, and let `A` be a separable nuclear `C_0(X)`-algebra whose nonzero
fibres are simple, non-AF and Z-stable.  The field may be arbitrary
upper-semicontinuous.  Then

```text
A tensor Z isomorphic to A,                                  (ZFF1)
1 <= dim_nuc(A) <= 2 dim(X)+1.                               (ZFF2)
```

The lower bound applies when `A` is nonzero.  In particular, when
`dim(X)<=1`,

```text
1 <= dim_nuc(A) <=3.                                         (ZFF3)
```

More precisely, if

```text
iota_A:A -> A tensor Z,       iota_A(a)=a tensor 1_Z,
```

then global Z-stability gives the exact identity

```text
dim_nuc(A)=dim_nuc(iota_A).                                  (ZFF4)
```

Consequently the desired one-dimensional conclusion is exactly the claim
that this generally nonsimple first-factor map has nuclear
dimension at most one.  Fibrewise application of the simple
nuclear-dimension theorem does not establish that map statement.

This gap is present before any upper-semicontinuous or twisting phenomenon.
The constant field

```text
C([0,1]) tensor Z                                             (ZFF5)
```

has simple non-AF Z-stable fibres and lies in the class above.  Tikuisis and
Winter proved the stronger-than-nuclear estimate

```text
dr(C(Y) tensor Z)<=2                                         (ZFF6)
```

for every compact Hausdorff `Y`, but their theorem does not replace `2` by
`1`.  Thus any blanket proof that fibrewise Z-stability forces
`dim_nuc(A)<=1` would already sharpen the published dimension-reduction
theorem on the canonical trivial interval field.  Globalizing absorption,
or citing the simple fibre theorem pointwise, is therefore not such a
proof.
