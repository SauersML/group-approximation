---
rg: 2
id: binary-jacobson-constant-weyl-target-redesign-proof
kind: route
title: Enumerate the two constant slots and test the moved Q-centers against the head cut
target: binary-jacobson-constant-weyl-target-redesign-moves-off-residual
requires:
  - binary-jacobson-head-sector-has-native-two-qubit-packet
  - binary-jacobson-native-v4-polar-orbit-leaves-one-residual
---

For a permutation `sigma` of the four coordinate indices, conjugation of
`(JWT1)` gives

```text
(x_(sigma1,sigma2)(Q), x_(sigma2,sigma3)(1),
 x_(sigma1,sigma4)(Q), x_(sigma4,sigma3)(1)),             (1)
```

with common center `x_(sigma1,sigma3)(Q)`.

The root `x_31(1)` can only be one of the two coefficient-one entries.
If it is the second entry, then

```text
sigma(2)=3,       sigma(3)=1.
```

The unused values for `sigma(1),sigma(4)` are `2,4`, so the center is
`x_21(Q)` or `x_41(Q)`.  If `x_31(1)` is the fourth entry, the same argument
uses `sigma(4)=3,sigma(3)=1` and gives the same two possible centers.  This
proves `(JWT2)`, while the displayed three-cycle proves `(JWT3)`.

The moved centers are conjugate to `w` as abstract marked roots, but their
reduction of the residual carrier is not a consequence of the defining
cuts.  The Steinberg commutator formulas give

```text
[x_21(Q),x_13(Q)]=x_23(Q^2)=x_23(Q)!=1,
[x_41(Q),x_13(Q)]=x_43(Q^2)=x_43(Q)!=1.                 (2)
```

The nontriviality follows in the faithful Jacobson matrix action.  To rule
out the possibility that the *additional* residual cuts make this
commutator vanish universally, use the left regular representation.  Let
`N` be the elementary abelian root subgroup whose character idempotent is
`e_res`.  Its elements have root support only in positions `(1,3)` with
coefficients in the controlled span and in position `(2,3)` with coefficient
`0` or `ST`.  But conjugation of `w` by the two moved centers gives

```text
x_21(Q) w x_21(Q)=x_23(Q)w,
x_41(Q) w x_41(Q)=x_43(Q)w.                              (3)
```

Neither right side belongs to `N`: the first has `(2,3)` coefficient `Q`,
not `0` or `ST`, and the second has a nonzero `(4,3)` component.  Therefore
neither moved center normalizes `N`.  The Fourier support of `e_res` is
exactly `N`, whereas the support of `m e_res m^(-1)` is `mNm^(-1)`.
Consequently these two projections differ in the left regular
representation, so `[m,e_res]!=0` there.  A negative cut for `(JWT2)` is new
carrier data, not a renaming of the established residual.  Notice that this
proves absence of a universal reduction identity; a special quotient could
still make the commutator vanish.

Finally a constant Weyl element only permutes matrix units:

```text
W_sigma x_ij(r) W_sigma^(-1)=x_(sigma i,sigma j)(r)       (4)
```

in characteristic two.  Thus the coefficients in every conjugate `(1)`
are still `Q,Q,1,1`; none is `T`.  More strongly all words in this finite
packet have entries in `F_2[Q]={0,Q,1-Q,1}`.  The faithful Jacobson action
shows `T` is not in this subring: `T` is the backward shift, whereas every
element of `F_2[Q]` is diagonal for the decomposition
`F_2 delta_0 directSum span{delta_i:i>=1}`.  This excludes `x_21(T)` both as
a tuple entry and as an element of the conjugated packet, completing the
proof.
