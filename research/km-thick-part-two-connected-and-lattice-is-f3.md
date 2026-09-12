---
rg: 2
id: km-thick-part-two-connected-and-lattice-is-f3
kind: claim
title: The bottom thick part of the (2,4,6) twin-building product is 2-connected, so the lattice is of type F_3 and its group-ring H2 is the compactly supported H2 of the thick part
distinct_from:
  km-codistance-filtration-twisted-levels-are-rank-two-pairs: that is the established structure of the filtration; this is the consequence for the bottom level, conditional on the finite surjectivity input.
  km-development-has-nonzero-end-cohomology-in-degree-one: that asks for nonvanishing of the group-ring `H^2`; this identifies that group with `H^2_c` of a 2-connected four-dimensional model without deciding whether it vanishes.
  simple-kazhdan-kac-moody-lattices-exist: that records finite presentability (type `F_2`) from Caprace--Rémy and Abramenko--Mühlherr; this is the next finiteness property `F_3`, not in the recorded literature for compact hyperbolic type.
---

**OPEN (final status 2026-08-23: the reducing input
`km-twisted-level-product-cycles-surject` failed only at small `q`
(`q <= 3` for hexagon levels, `q = 3` for `B_2`), by curve-span
thresholds vacuous for `q > 1764^3`; for the actual lattices the
route through it is LIVE again and expected to close, in any
characteristic, once the disjoint-class bookkeeping is written).**  Let
`X^ = Z_(<=0)` be the union of the closed product cells `x x y` over
opposite chamber pairs of the `(2,4,6)` twin building, a cocompact
proper simply connected `Lambda`-complex of dimension four.  Then

```text
H_1(X^;Z) = H_2(X^;Z) = 0,                                   (TP1)
```

so `X^` is 2-connected, `Lambda = Lambda_(2,4,6)(q)` is of type `F_3`
(Brown's criterion), and

```text
H^2(Lambda; Z Lambda) = H^2_c(X^; Z) = H^3_c(Z minus X^; Z),     (TP2)
```

the second equality from the sequence of the closed subcomplex
`X^ <= Z = X_+ x X_-` and `H^2_c(Z)=H^3_c(Z)=0` (Künneth and the
top-degree concentration of the compactly supported cohomology of the
two buildings).

Route: `km-thick-part-two-connected-via-twisted-surjectivity`.  The
`F_3` statement would be new: the recorded literature (Rémy's survey,
Abramenko--Mühlherr) gives only finite presentability for these
lattices; the affine analogue `SL_3(F_q[t,t^(-1)])` is `F_3` by the
Bux--Köhl--Witzel rank theorem.

**Warning on the sign of the consequence.**  The same input computes
the right-hand side of `(TP2)` to be ZERO: every cusp level has
cohomology only in degree four, so a downward induction gives
`H^3_c(Z minus X^)=0` (details in
`km-cusp-region-has-degree-three-compact-cohomology`).  So this claim,
once established, REFUTES the nonvanishing claims downstream and kills
the Corollary D route, rather than feeding it.
