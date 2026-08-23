---
rg: 2
id: low-gap-cut-and-spike-dichotomy-holds-for-contractions
kind: claim
title: Low-gap coarea and clipping survive nested compression to contractions
distinct_from:
  bounded-low-gap-witness-gives-balanced-cut: that states the result for unitary generators; this observes that its proof only needs operator-norm-one contractions and hence can be iterated without intermediate polar signs
  low-gap-witness-spike-or-balanced-cut: that states one unitary-level clipping dichotomy; this supplies the contraction-level version required by a Pythagorean cut tree
---

Both `bounded-low-gap-witness-gives-balanced-cut` and
`low-gap-witness-spike-or-balanced-cut` remain valid, with the same
constants, when the unitaries `u_s` are replaced by arbitrary contractions
`A_s` with `||A_s||_op<=1`.

Consequently, after a common cut, the recursion may continue directly with
the compressed contractions

```text
e Q_i e
```

inside every child corner.  No intermediate polar sign is required to
obtain the next low-gap spectral cut or spike.  The entire nested tree can
therefore retain the exact Pythagorean boundary ledger, and all contractions
may be signed simultaneously only after the terminal PVM is chosen.

## Attempts

A proof by unitary conjugation of the clipped witness appears not to survive
compression.  In Hilbert--Schmidt norm that conjugation argument is
unnecessary: the eigenbasis divided-difference calculation controls
`[A,f(x)]` for every contraction `A`.  This is special to the `L_2` norm and
does not assert operator-norm Lipschitz functional calculus.
