---
rg: 2
id: atlas-collision-fiber-symmetrization-fence-proof
kind: route
title: Use packet generation, opposite phases, and the zero Haar barycenter
target: atlas-collision-fiber-has-no-block-symmetrization
requires:
  - atlas-a4-packet-letters-generate-both-a8-charts
  - atlas-repeated-collision-fiber-is-two-block-procrustes
---

The packet-generation theorem gives

```text
<S_pkt>=A8.
```

An operator commuting with every packet coefficient therefore commutes with
the whole regular `A8` representation.  This proves `(SYM2)` and shows that
the `K`-multiplicity group is strictly too large to act as a coefficient
symmetry.

Every stored packet word is a six-syllable pair cube and contains three
second-chart syllables.  Substitution of `X=0` therefore makes its product
zero.  At `R` and `-R` the scalar signs cancel inside each conjugation, while
`R` is the exact packet alignment.  This proves `(SYM3)--(SYM4)` directly.

For `(SYM5)`, scalar phases commute with `rho(b_0)` and cancel in
`(zU)^*rho(b_0)(zU)`.  They also cancel in every second-chart conjugate, so
the whole phase circle remains in one collision fiber and on one packet-energy
level.  Its Haar integral is zero.  Since zero has no polar unitary, no polar
repair can be selected from the averaged operator without adding external
data; in particular no norm or energy estimate follows from averaging.

Lastly, left multiplication by `rho(A8)'` preserves both the packet energy and
the fixed collision fiber, but has the zero barycenter above.  Conjugation by
that group has fixed points `rho(A8)''`, not the repeated `K`-block algebra,
and it generally sends the fixed collision observable `c` to `D c D^*`.
These observations exhaust both possible uses of averaging here: the desired
large averaging group is not a symmetry, while the actual fiber symmetry
loses unitarity under linear averaging.
