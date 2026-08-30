---
rg: 2
id: stw93-residual-extension-splits-over-factor
kind: claim
title: The saturated XCIII residual extension splits over the Jiang--Su factor section
distinct_from:
  stw93-jiang-su-slice-exhausts-tracial-central-quotient: that theorem identifies the quotient D/I with F(Z)/J and gives D=I+iota(F(Z)); this theorem descends the slice through the larger saturated ideal and obtains an injective star-homomorphic section of the residual extension.
  stw93-residual-tracefree-iff-unique-trace: that theorem characterizes existence of an extra ordinary trace through bounded traces on the residual ideal; this theorem exposes the split factor action and the central support geometry of such a trace.
  stw93-saturated-slice-data-allow-residual-trace: that abstract doubled model has an evident direct-sum splitting; this theorem proves a canonical semidirect splitting in the actual XCIII central sequence algebra without asserting that its residual ideal is traced.
artifacts:
  - research/artifacts/stw93-residual-factor-section-audit-2026-08-30.md
---

Put

```text
D=(C*_r(F_2) tensor Z)_omega intersect (C*_r(F_2) tensor Z)',
I=J_tau intersect D,               E=D/K_Z^sat,
R=I/K_Z^sat,                       G=F(Z),
J=J_(tau_Z) intersect G,           Q=G/J.
```

The extension

```text
0 -> R -> E -> D/I -> 0                                  (1)
```

has a canonical unital star-homomorphic section

```text
s:Q -> E.                                                (2)
```

Under the established isomorphism `Q~=D/I`, the quotient map in `(1)`
composed with `s` is the identity.  Consequently

```text
E=R+s(Q),                       R intersect s(Q)={0},     (3)
```

and every element of `E` has a unique decomposition `r+s(x)`.  This is a
split C*-extension, not a claim that `R` and `s(Q)` commute or that `E` is a
direct-product algebra.

Every normalized trace on `E` restricts to the canonical factor trace on
`s(Q)`.  Hence a negative ordinary-trace witness is precisely a second
finite extension of that same factor trace which charges `R`; it cannot
change the quotient representation.

The splitting does not imply that every quasitrace on `E` is linear and
does not prove that `R` is trace-free.
