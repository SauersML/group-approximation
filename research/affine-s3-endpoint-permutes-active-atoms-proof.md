---
rg: 2
id: affine-s3-endpoint-permutes-active-atoms-proof
kind: route
title: Realize the forbidden-point stabilizer and induce from one active character
target: affine-s3-endpoint-permutes-active-atoms
requires:
  - s3-active-complement-is-three-equal-scale-affine-atoms
  - finite-schur-clifford-packet-flexible-hs-exactification
  - shared-overlap-controls-packet-multiplicity-vector
---

On the `J=-1` carrier write

```text
K=(-1)^k,                  b=(-1)^ell,
```

so the forbidden atom is `(k,ell)=(1,1)`.  The two maps in `(ASE2)` induce

```text
s:(k,ell) |-> (k,1+k+ell),
u:(k,ell) |-> (1+k+ell,ell).                             (1)
```

Each is a transposition of two of the points

```text
(0,0), (0,1), (1,0),                                      (2)
```

fixes the remaining point and `(1,1)`, and together they generate all six
affine permutations fixing `(1,1)`.  Direct substitution gives
`s^2=u^2=(su)^3=1`, both on `D` and on its character plane.  This proves
`(ASE2)--(ASE3)` and the transitivity assertion.

Let the three active character spaces have common rank `r`; conjugacy under
the displayed `S_3` proves equality of their ranks.  Fix one of them.  Its
stabilizer in `S_3` has order two, and its involution splits that `r`-space
into `+` and `-` spaces of ranks `r_+` and `r_-`.  The active part of the
`C_aff`-representation is the direct sum of the two induced orbit
representations, with multiplicities `r_+` and `r_-`.  Hence

```text
dim End_(C_aff)(A C^d)=r_+^2+r_-^2
                     >=(r_++r_-)^2/2=r^2/2.             (3)
```

Since `ad=3r`, division by `d^2` turns `(3)` into

```text
r^2/(2d^2)=a^2/18,
```

which is `(ASE4)`.

The normal-form theorem for a free product with amalgamation embeds both
finite factors in `(ASE5)`.  For the completeness assertion, induce any
unitary `B`-representation `pi` with `pi(J)=-I` from `B` to `G_aff`.  The
element `J` is central in both factors and hence in the amalgam, and the
covariance relation in the induced representation gives `Ind(pi)(J)=-I`.
No finite multiplicity extension is required.

Finally, `C_aff` is one fixed finite group.  Its approximate multiplication
table and the endpoint table may therefore be exactified with constants
independent of ambient dimension.  Spectral projection perturbation changes
the active carrier mass by `O(sqrt(E))`; applying `(ASE4)` to the exactified
carrier gives the stated robust form.
