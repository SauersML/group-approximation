---
rg: 2
id: modular-vertex-extension-does-not-force-congruence
kind: claim
title: Extension through a modular vertex does not force a congruence packet
distinct_from:
  mixed-crt-iwahori-repair-is-labeled-pure-dyadic-rounding: that reduces pairs already factoring through congruence quotients to labeled dyadic rounding; this shows that the vertex-extension hypothesis produced by outlier localization does not put a pair in that class.
  residual-finite-tensor-camouflages-iwahori-transfer-failures: that makes any tensor-stable failed pair have canonical trace; this gives an exact representation-theoretic obstruction before trace conditioning.
  edge-pair-mixed-gap-collapse: that additionally assumes a collapsing mixed gap for a pair of opposite extendible edge types; this isolates why extendibility alone supplies no congruence reduction.
---

Let `C=SL_2(Z)` and let `B<C` be either index-three Iwahori subgroup.
There are irreducible finite-dimensional unitary representations `pi_n` of
`C`, of dimensions tending to infinity, whose images are infinite.  For
each `n`, the restriction `pi_n|B` has an irreducible constituent `theta_n`
such that

```text
dim(theta_n) >= dim(pi_n)/3                             (MVC1)
```

and `theta_n(B)` is infinite.  Thus `theta_n` is a high-dimensional edge
irreducible extending through an exact modular vertex representation, but
it does not factor through a finite quotient, hence not through a
congruence quotient.

Consequently the high-dimensional edge pairs supplied by
`iwahori-outlier-localization` are not necessarily among the exact
congruence packets closed by
the mixed-CRT and odd-label congruence repair theorems.  The additional
near-intertwining/mixed-gap hypothesis might still force congruence
proximity; proving that is a new relative exactification theorem, not a
formal consequence of modular extension.

Canonical trace does not supply the missing implication either.
`residual-finite-tensor-camouflages-iwahori-transfer-failures` tensors any
candidate pair with separating finite-quotient regular representations,
making every fixed-word trace canonical while preserving its normalized-HS
edge geometry.  Selberg property `(tau)` controls representations already
on the congruence side; it does not project arbitrary modular
representations into the congruence locus.
