---
rg: 2
id: nonhyperlinear-directly-from-fixed-pi-fingerprint
kind: route
title: The fixed PI fingerprint itself gives the terminal HS contradiction
target: non-hyperlinear-group
requires:
  - leavitt-regular-atlas-hyperlinearity-criterion
  - fixed-pi-degree-fingerprints-packet-label-factor
---

Assume the regular-atlas Leavitt group were hyperlinear and take the canonical
matrix microstates supplied by
`leavitt-regular-atlas-hyperlinearity-criterion`.  Apply
`fixed-pi-degree-fingerprints-packet-label-factor` on its positive-density
corner `P`.  The source packet gives

```text
||s_(2r)(X^(n))||_2=o(1),                              (PIR1)
```

the closed transport gives

```text
||s_(2r)(X^(n))-s_(2r)(Y^(n))||_2=o(1),                (PIR2)
```

and the transverse target packet gives

```text
||s_(2r)(Y^(n))||_2
  >=sqrt(alpha) kappa_r-o(1).                          (PIR3)
```

The triangle inequality contradicts `alpha>0` and `kappa_r>0`.

No mutual-bicommutant or scalar joint-fullness conclusion is used.  A common
tensor spectator leaves every evaluation in `(PIR1)`--`(PIR3)` unchanged.
Thus the refutation of scalar spectator elimination does not invalidate the
fixed-PI terminal; it only says that the packet construction must establish
the three PI hypotheses directly on one carrier rather than derive them from
mutual commutants.
