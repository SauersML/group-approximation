---
rg: 2
id: ah-groups-fail-regular-fd-character-rigidity
kind: claim
title: Acylindrically hyperbolic groups cannot have regular-or-finite-dimensional factor-character rigidity
distinct_from:
  factor-universality-character-rigidity-implies-nonhyperlinear: that is a valid conditional compiler; this proves the CDI acylindrically-hyperbolic source class can never supply its rigidity hypothesis.
  cdi-character-cannot-be-promoted-by-regular-corners: that rules out standard trace-promotion operations for one CDI character; this gives an intrinsic quotient character obstructing the proposed rigidity.
---

Every acylindrically hyperbolic group `H` has a proper infinite ICC quotient
`q:H->Q` after a sufficiently deep group-theoretic Dehn filling (and, if
needed, quotienting the finite radical).  Pull back the regular character of
`Q`:

```text
chi(h)=delta_e(q(h)).                                   (AHC1)
```

Because `Q` is ICC, `chi` is extremal with infinite-factor GNS algebra
`L(Q)`.  It is not the regular character of `H`, since it equals one on the
nontrivial kernel of `q`, and it is not finite dimensional.  Hence no
acylindrically hyperbolic group satisfies the regular-or-finite-dimensional
factor-character rigidity used by the conditional factor compiler.

The quotient input is the standard Dahmani--Guirardel--Osin/Hull Dehn-filling
consequence for acylindrically hyperbolic groups.  This strengthens the
weaker observation that no currently cited group is known to satisfy both
properties: the CDI source class and this rigidity hypothesis are
structurally incompatible.

This no-go does **not** exclude faithful factor-character rigidity.  Every
character `(AHC1)` has kernel `ker(q) != {e}`.  The canonical-trace bridge for
the actual CDI image has consequently been sharpened in
`cdi-image-quotient-off-regular-characters-are-ce`: it needs to classify only
faithful nonregular factorial characters.  Acylindrical-hyperbolic quotient
characters disappear from that restricted face.
