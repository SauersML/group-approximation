---
rg: 2
id: alternating-free-ring-shears-have-strict-degree-drift
kind: claim
title: Two alternating free-ring shears give a strict linear degree clock
artifacts:
  - experiments/alternating_free_ring_shear_degree.py
distinct_from:
  paired-frame-hard-characters-form-forced-two-cycle: that proves the finite character coordinate returns after two transports; this supplies an infinite polynomial-degree coordinate which never returns.
  one-sided-paired-frame-reverse-reservoir-collapse: that still has to place the packet character carriers in orthogonal spectral valuation layers; this proves the exact algebraic drift of the proposed transporter.
---

Over `F_2[x]`, put

```text
A = [[1,x],[0,1]],     B = [[1,0],[x,1]],
T = A B = [[1+x^2,x],[x,1]].                            (ASD1)
```

Although `A^2=B^2=I`, their alternating product has strict degree drift.  For
every `n>=1`, the entrywise polynomial degrees are

```text
deg(T^n) = [[2n, 2n-1], [2n-1, 2n-2]],                 (ASD2)
```

and every displayed leading coefficient is one.  In particular, the orbit
of either coordinate vector under `T` acquires a new highest degree at every
step.

Both factors in `(ASD1)` are precisely the adjacent elementary shears already
realized by conjugation on the coefficient planes of
`EL_3(F_2<x>)`.  Acting diagonally on the `p` and `q` coefficient pairs gives
the same algebraic shape as the two simultaneous word shears in `(PWF1)`.
This makes available the following candidate decoration of two finite
hard-character flips:

```text
(101, degree 2n) -> (011, degree 2n+1)
                  -> (101, degree 2n+2).                (ASD3)
```

Equation `(ASD3)` is an algebraic nonreturn mechanism: the finite character
returns, but the full character-plus-degree label does not.  Turning distinct
degrees into orthogonal matrix carriers, and proving that the paired packet
actually follows this decorated action, are separate spectral-placement
obligations; `(ASD3)` records the proposed coupling, not an additional
conclusion of `(ASD2)`.
