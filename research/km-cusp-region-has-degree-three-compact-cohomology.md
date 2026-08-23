---
rg: 2
id: km-cusp-region-has-degree-three-compact-cohomology
kind: claim
title: The positive-codistance cusp region of the (2,4,6) twin-building product has nonzero compactly supported cohomology in degree three
distinct_from:
  km-thick-part-two-connected-and-lattice-is-f3: that identifies the group-ring `H^2` with `H^2_c` of the thick part; this is the nonvanishing of that group, rewritten on the cusp side.
  km-development-has-nonzero-end-cohomology-in-degree-one: that is the same nonvanishing expressed on the two-dimensional development as end cohomology; this is its expression on the complement of the four-dimensional thick part, where Borel--Serre-type reduction theory should apply.
---

**OPEN.**  With `Z = X_+ x X_-` and `X^ = Z_(<=0)` the bottom thick part,
prove

```text
H^3_c( Z minus X^ ; Z ) != 0,                                   (CR1)
```

equivalently (given `km-thick-part-two-connected-and-lattice-is-f3`)
`H^2(Lambda;Z Lambda) != 0`, so that Ioana--Spaas--Wiersma Corollary D
applies to `C^*(Lambda_(2,4,6)(q))`.

The cusp region `Z minus X^` is the open union of the product cells of
chamber pairs at positive codistance length; its `Lambda`-orbits of
top cells are indexed by `W minus {1}`.  In the arithmetic analogue
(`SL_3(F_q[t,t^(-1)])`) the corresponding region is governed by the
rational parabolic subgroups; no twin-building reduction theory for it
is recorded.  A positive answer is expected by analogy with
`titz-witzel-lattices-fail-lp`, where the lattice is uniform and the
model contractible; a negative answer would leave the LP question at
the Kac--Moody lattices undecided by every Ioana--Spaas--Wiersma clause
except the `L^0` one (`triangle-colimit-rational-h2-vanishes`).
