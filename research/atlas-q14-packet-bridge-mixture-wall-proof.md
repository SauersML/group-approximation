---
rg: 2
id: atlas-q14-packet-bridge-mixture-wall-proof
kind: route
title: Balance the two opposite residual densities and compute the linear-action permutation trace
target: atlas-q14-packet-bridge-mixtures-have-uniform-wall
requires:
  - atlas-square-root-frame-has-unit-packet-residual
  - atlas-packet-collision-m2-has-full-coefficient-algebra
  - atlas-q14-growing-width-rank-one-bridge-is-sharp
---

The square-root-frame theorem supplies one fixed `H18` packet word `w_*`
whose residual on `Q_n` is a natural transvection of rank `n`; q14 is exact
there.  The multiplicity-two theorem supplies exact packet and collision on
`P`, while its q14 residual has rank one.  Amplification by `I_k` multiplies
that rank by `k`.  Block additivity proves `(QPM2)`.

Write

```text
lambda=4n/D.
```

At `T_0` the normalized ranks of the two residuals are respectively

```text
lambda/4,                    (1-lambda)/8.             (QMPP1)
```

Their maximum is minimized when the two numbers are equal, namely at
`lambda=1/3`, and the common value is `1/12`.

The triangle inequality for rank gives

```text
rank(T-T_0)<=r.                                       (QMPP2)
```

For invertible frames, inverse differences have the same rank.  If a fixed
word contains `ell` second-chart syllables, telescoping its evaluation one
frame or inverse occurrence at a time gives

```text
rank(w(T)-w(T_0))<=2 ell r.                           (QMPP3)
```

Take `L` to be the larger syllable count for `w_*` and q14.  Combining
`(QMPP1)--(QMPP3)` proves `(QPM4)`.  The same calculation depends only on
the total dimensions of the two block types, so it covers arbitrary direct
sums and passive tensor amplifications.

For the permutation lift, the fixed vectors of `A` are exactly
`ker(A-I)`, of cardinality

```text
2^(d-rank(A-I)).                                      (QMPP4)
```

The normalized trace of its permutation unitary is therefore
`2^(-rank(A-I))`.  Since this trace is real,

```text
||U_A-I||_2^2=2-2 Re tr(U_A)
             =2(1-2^(-rank(A-I))),                   (QMPP5)
```

which is `(QPM5)`.  A nonzero source rank gives energy at least one.  In a
Hilbert direct sum, now writing `lambda` for the Hilbert-dimension weight of
the q14 phase, the packet energy is at least `lambda` and the packet-phase
q14 energy is at least `1-lambda`; their maximum is at least `1/2`.  The raw
linear action on all vectors is not literally the prescribed regular-`A8`
chart carrier.  A negligible finite-group carrier correction cannot remove
the displayed positive residual energy.
