---
rg: 2
id: c3-payload-defeats-selector-normalizer-correctors
kind: claim
title: A three-character zero-compression payload defeats every selector-normalizer corrector
invalidates:
  - arbitrary-selector-normalizer-wordizes-stabilizer-corrector
distinct_from:
  selector-normalizer-corrector-has-an-atom-permutation-criterion: that gives an exact positive criterion for block-monomial payloads and a permutation obstruction inside that face; this gives a dense orthogonal payload for which even the full selected-atom MASA normalizer has no corrector.
  selector-packet-central-corrector-fails-on-a-three-cycle: that excludes only packet-central correctors and explicitly retains a normalizer corrector; this excludes all selector normalizers fixing the selected atom.
  extraspecial-fourier-zero-cell-is-fixed-face-pruning: that uses an invariant character fixed face of a specific shear normalizer; this is a three-dimensional modulus-symmetry obstruction requiring no fixed-face argument.
---

**ESTABLISHED.**  Let `H=C_3` act on `C^3` as the direct sum of its three
distinct characters, with joint character basis `e_0,e_1,e_2`, and put
`q=|e_0><e_0|`.  Define

```text
u=(3/5,4/5),                 u_perp=(-4/5,3/5),
v=(5/13,12/13),              v_perp=(-12/13,5/13),       (TNC1)
```

and, in the decomposition `C e_0 direct-sum span(e_1,e_2)`, let

```text
W = [ 0       v^T              ]
    [ u       u_perp v_perp^T  ]

  = [ 0     5/13    12/13 ]
    [ 3/5   48/65  -20/65 ]
    [ 4/5  -36/65   15/65 ].                              (TNC2)
```

Then `W` is a real orthogonal matrix and `qWq=0`, but there is no unitary
`S` normalizing the represented selector group `H` for which `SW` is an
involution.

## Proof

The two vectors in each pair in `(TNC1)` are orthonormal.  The first row of
`W` has norm one.  Its inner product with either lower row is a scalar
multiple of `v dot v_perp=0`, while the Gram matrix of the two lower rows is

```text
u u^T + u_perp u_perp^T=I_2.                              (TNC3)
```

Thus the rows of `W` are orthonormal.  Its `(0,0)` entry is zero, proving
`qWq=0`.

The represented generator of `C_3` has the three distinct eigenvalues
`1,omega,omega^2`.  A unitary normalizing this cyclic subgroup conjugates
the generator either to itself or to its inverse.  Hence, up to arbitrary
row phases, left multiplication by `S` either preserves all three character
rows or swaps rows `1` and `2` while fixing row `0`.  These are also all
permutations in the normalizer of the full diagonal selector algebra which
fix `q`.

If the unitary `U=SW` were an involution, then

```text
U=U^-1=U^*,                 hence |U_ij|=|U_ji|.          (TNC4)
```

In the row-preserving case,

```text
|U_01|=5/13,                      |U_10|=3/5;             (TNC5)
```

in the row-swapping case,

```text
|U_01|=5/13,                      |U_10|=4/5.             (TNC6)
```

Row phases do not alter these moduli, and both cases contradict `(TNC4)`.
Therefore no selector-normalizer corrector exists.

By `stabilizer-corrector-hermitianizes-zero-compression`, an unrestricted
unitary stabilizing only `q` nevertheless does correct this `W`.  Thus the
failure is exactly the attempt to keep the corrector inside the selector
normalizer.  It does not refute the unrestricted selected-projection
corrector or settle the main typewise payload-sensitive nontransport
holonomy readout, which may leave the selector normalizer.
