---
rg: 2
id: nonhyperlinear-from-pauli-overlap-dichotomy
kind: route
title: Compulsory Pauli overlap plus a holonomy-or-transverse dichotomy forbids microstates
target: non-hyperlinear-group
requires:
  - atlas-steinberg-rank-five-translation
  - pauli-packet-incoming-mass-exceeds-corner-capacity
  - mixed-relations-force-holonomy-or-transverse-recovery
  - contraction-branch-capacity-forces-collision
  - fixed-holonomy-on-overlap-pays-relator-energy
  - tensor-independent-child-carrier-gap
---

`atlas-steinberg-rank-five-translation` fixes the explicit finite atlas group
`Gamma_St`.  Suppose it were hyperlinear; take trace-preserving
finite-dimensional microstates with atlas relator defect `delta_n -> 0`.

By `pauli-packet-incoming-mass-exceeds-corner-capacity` the two transported
coefficient involutions carry mass `M_tot = 5/8` into the corner `Q` of trace
`1/2`, so the reproduction number is `5/4 > 1` and
`contraction-branch-capacity-forces-collision` forces ordered cross-Gram overlap
at least `M_tot^2/q - M_tot = 5/32`.  This is compulsory and dimension-free;
it is not yet a contradiction, since the exact model pays it too.

`mixed-relations-force-holonomy-or-transverse-recovery` then splits on what the
mixed `A_4`/`A_8` relations do with that overlap, on a subcorner of trace at
least `c`:

- **Branch (HOL).**  Two fixed relator words act on the subcorner as
  `U tensor H_1`, `V tensor H_2` with `U,V` distinct `S_3` reflections.  By
  `(FHO3)` of `fixed-holonomy-on-overlap-pays-relator-energy`,
  `||[X,Y]-1||_2^2 >= c`, and `[X,Y]` is a fixed word in the presentation, so
  the relator defect is bounded below by `c` -- contradicting `delta_n -> 0`.
- **Branch (TRV).**  One common projection `F` of trace at least `c` lies within
  `kappa` of both the raw and the comb child algebras, which are
  trace-independent.  By `tensor-independent-child-carrier-gap`,
  `dist_2(F,A)^2 + dist_2(F,B)^2 >= c(1-c)`, so `2 kappa^2 >= c(1-c)` and
  `kappa` is bounded below.  Since `kappa` is controlled by the relator defect,
  this again contradicts `delta_n -> 0`.

Both branches give a fixed positive floor, so `Gamma_St` is not hyperlinear.

**What this route is and is not.**  Compared with
`nonhyperlinear-from-fractional-pauli-pressure`, which needs a whole weighted
network with reproduction number above one, this route needs supercriticality at
a *single corner* and puts all remaining weight on the dichotomy.  Both of its
premises are open and the first is worse than open: the mass budget `(PIM1)` is
an assertion from outside this repository which a grep of `notes/` does not
confirm, so the route is stated with that dependency explicit rather than
folded into prose.  The two constants it produces, `5/32` and `c(1-c)`, are
dimension-free, which is the property a non-hyperlinearity proof ultimately
needs.
