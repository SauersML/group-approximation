---
rg: 2
id: even-weil-fixed-line-compression
kind: claim
title: The even Weil fixed line compresses to an O(p^-1/2) Iwahori near-extension with exact BS14 core
distinct_from:
  prime-bs14-packet-extension-classification: that classifies exact scalar packets; this constructs a reducible exact BS core with no same-dimensional extension but vanishing presentation defect.
  bs14-relative-involution-extension-stability: that allows flexible padding; this proves such padding is essential and identifies the sharp one-dimensional boundary model.
  iwahori-cycle-packet-determinant-fence: determinant detects exact nonextension but cannot prevent this normalized-HS compression.
---

For every prime `p=1 mod 4`, the even Weil representation of
`PSL_2(F_p)` has dimension

```text
d=(p+1)/2
```

and, on the arithmetic BS(1,4) subgroup, splits as

```text
H = C delta_0 (+) H_0,       dim H_0=(p-1)/2.          (EWC1)
```

The line `C delta_0` is fixed by the parabolic `S` and preserved by the
diagonal implementer `R`; `H_0` is the sum of the nonzero fourth-power
spectral cycles.  Let `P` project onto `H_0`, let `Q=1-P`, and write the full
Weil involution as `X`.  Then

```text
A=PXP,
A^2-P=-P X Q X P,                                   (EWC2)
```

whose right side has rank at most one.  Functional calculus gives a
selfadjoint involution `X_0=sgn(A)` on `H_0` with

```text
||X_0-A||_(2,H_0) <= 1/sqrt(dim H_0).                 (EWC3)
```

In fact the polar deficiency is exactly one-dimensional.  In the normalized
Schrodinger model `|<delta_0,X delta_0>|=p^(-1/2)`, so `A` has one singular
value `p^(-1/2)` and every other singular value is one.  Therefore

```text
||X_0-A||_(2,H_0)
  =(1-p^(-1/2))/sqrt((p-1)/2).                         (EWC3')
```

Thus neither the polar step nor the deleted-line coupling hides an
additional diffuse error: the whole boundary mode has rank one and the
repair cost is sharply of order `p^(-1/2)`.

The polar correction also preserves the dihedral relation exactly:

```text
X_0 R X_0=R^(-1).                                    (EWC3'')
```

Hence the compressed boundary model has no residual on `X^2=1` or
`(XR)^2=1`; all presentation defect is confined to the two modular cubic
constraints.

Because `R,S` preserve `P`, compressing any one of the four fixed Iwahori
words loses only excursions through the one-dimensional `Q` corner.  Word
telescoping and `(EWC3)` therefore give a universal constant `C` such that

```text
max( ||X_0^2-I||_2,
     ||(X_0R)^2-I||_2,
     ||(X_0S^2)^3-I||_2,
     ||(X_0RS)^3-I||_2 )
  <= C/sqrt(p).                                       (EWC4)
```

The BS core `(R,S)|_(H_0)` is exact.  It has no exact same-dimensional
Iwahori extension: `S` has primitive `p`-spectrum, so any such extension
would factor through `PSL_2(F_p)`, whose smallest nontrivial complex degree
is `(p+1)/2>dim H_0`.  Adding back the single line `C delta_0`, however,
recovers the exact Weil representation.

There is in fact a constant `c>0`, independent of `p`, such that for all
large `p=1 mod 4`, the tuple on `H_0` is at generator distance at least `c`
from **every** exact Iwahori representation of dimension `(p-1)/2`.  To see
this, let `pi_p` be the irreducible full even Weil representation and suppose
an exact same-dimensional representation `sigma_p` approached the compressed
tuple.  Then `sigma_p (+) 1` would approach `pi_p`, because adjoining one
trivial line changes the compressed tuple to `pi_p` by only `O(p^(-1/2))`.
Property `(T;FD)` of `PSL_2(Z[1/2])` gives a uniform spectral gap on the
finite-dimensional conjugation representation

```text
pi_p tensor conjugate(sigma_p (+) 1).
```

Two sufficiently close exact tuples would therefore have a nonzero
intertwiner.  Since `pi_p` is irreducible and both sides have dimension
`(p+1)/2`, this would make `sigma_p (+) 1` isomorphic to `pi_p`, impossible
because the former has an invariant line.  Thus these tuples are an explicit
strict-HS-instability sequence even though they are flexibly repaired by one
dimension.

## Meaning for the open repair problem

Same-dimensional metric repair is uniformly impossible, while one-dimensional
flexible repair is explicit.  The proved cubic-defect estimate is
`O(d^(-1/2))`, while the evident arithmetic repair restores one dimension.
A matching `Omega(d^(-1/2))` lower bound for one of the two cubic words has
not been computed, so this alone does not identify the padding density with
the squared observed defect.  This does not refute the flexible
Dogon--Vigdorovich target: their generalized metric
allows the full `(p+1)/2`-dimensional Weil representation, which is
`O(p^(-1/2))` from the compressed tuple.  Any proposed positive-density
packet gap that forbids `(EWC4)` is false.

The missing lower estimate is now computed for `p=5 mod 8` in
`even-weil-second-cubic-has-a-rank-six-determinant-gap`: the second cubic
residual has rank at most six and determinant `-1`, so its normalized-HS norm
is at least `2/sqrt(6d)`.  Thus the `Theta(d^(-1/2))` defect and quadratic
one-line padding calibration are valid on that infinite subsequence.  The
same determinant argument is neutral for `p=1 mod 8`.
