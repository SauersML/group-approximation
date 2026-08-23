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

## Attempts

- **The twisted surjectivity REFUTES this claim (2026-08-23).**  Write
  `cusp_(<=R) = Z_(<=R) minus X^`, an increasing exhaustion of the cusp
  by open subsets with `C^*_c(cusp) = colim C^*_c(cusp_(<=R))`.  The
  quotient of consecutive stages is the level-`R` cochain complex, whose
  cohomology is `H^q(cl O_w, D)` summed over level-`R` residue pairs.
  Under `km-twisted-level-product-cycles-surject` every level has
  relative homology concentrated in degree four and free, so by
  universal coefficients `H^q(level R) = 0` for `q <= 3`.  Downward
  induction through the long exact sequences of the pairs gives
  `H^q_c(cusp_(<=R)) = 0` for `q <= 3` and all `R`, hence
  `H^3_c(Z minus X^) = 0` in the colimit, and with
  `H^2_c(Z)=H^3_c(Z)=0` (Künneth; the buildings' compactly supported
  cohomology is concentrated in degree two and free, DDJMO with the
  circle nerve of the `(2,4,6)` diagram),

      `H^2(Lambda; Z Lambda) = H^2_c(X^) = H^3_c(Z minus X^) = 0`.

  (The identification `H^2(Lambda;Z Lambda)=H^2_c(X^)` needs only
  `H_1(X^)=H_2(X^)=0`, not simple connectivity: the Cartan--Leray
  injectivity uses `H^1(X^;M)=0`, which follows from `H_1(X^)=0` by
  universal coefficients.)  So this claim is TRUE only if `(TLS1)`
  FAILS at some `G_2` or unforeseen twisted level; if `(TLS1)` holds --
  it is proved for the grid type and reduced to a pencil computation
  verified in the symplectic model for `B_2` -- then Ioana--Spaas--
  Wiersma Corollary D is DEAD at the `(2,4,6)` lattices, alongside the
  trivial-coefficient clause of Corollary E
  (`triangle-colimit-rational-h2-vanishes`).  The expected resolution
  is therefore the NEGATION of this claim and of
  `km-development-has-nonzero-end-cohomology-in-degree-one`, leaving
  the LP fork with no live Ioana--Spaas--Wiersma clause except the
  `L^0`-coefficient one.
