---
rg: 2
id: km-group-ring-h2-vanishes-for-the-lattices
kind: claim
title: The simple Kazhdan Kac-Moody lattices have vanishing group-ring second cohomology
artifacts:
  - research/artifacts/km-lattice-cohomology-and-lp-fork-2026-08-23.md
  - research/artifacts/km-opposition-connectivity-computations-2026-08-23.md
invalidates:
  - km-lp-fails-via-development-end-cohomology
  - km-end-cohomology-via-thick-part-compact-class
distinct_from:
  km-thick-part-two-connected-and-lattice-is-f3: that establishes the 2-connectivity of the thick part and identifies the group-ring `H^2` with its compactly supported `H^2`; this computes that group to be zero by the cusp induction.
  triangle-colimit-rational-h2-vanishes: that is the rational vanishing from the development alone; this is the integral group-ring statement, which needed the whole filtration analysis.
  km-development-has-nonzero-end-cohomology-in-degree-one: that conjectured the opposite; this establishes its negation, dead-ending the Ioana--Spaas--Wiersma Corollary D routes.
---

**THEOREM (established; proof in
`km-group-ring-h2-vanishes-proof`).**  For `Lambda = Lambda_(2,4,6)(q)`,
`q > 1764^3`, in any characteristic,

```text
H^2(Lambda; Z Lambda) = 0.                                     (GV1)
```

Consequently `km-development-has-nonzero-end-cohomology-in-degree-one`
and `km-cusp-region-has-degree-three-compact-cohomology` are REFUTED,
Ioana--Spaas--Wiersma Corollary D can never apply to these lattices,
and -- with `H^2(Lambda;R) = 0` from
`triangle-colimit-rational-h2-vanishes` -- the only known
Ioana--Spaas--Wiersma mechanism left for LP failure at the Kac--Moody
candidates is the `L^0(Y,R)` clause of their Corollary E.  The lattice
is also of type `F_3`
(`km-thick-part-two-connected-and-lattice-is-f3`), apparently a new
finiteness property for compact hyperbolic Kac--Moody groups.
