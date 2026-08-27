---
rg: 2
id: exact-torsion-frame-rank-one-counterpacket-proof
kind: route
title: Normalize the compressed even Weil packet and transport its strict separation
target: exact-torsion-frame-has-rank-one-strict-counterpackets
requires:
  - iwahori-two-triangle-torsion-normal-form
  - sl2-half-explicit-strict-flexible-separation
---

First compute the words.  The inversion row is equivalent, isometrically in
normalized Hilbert--Schmidt norm, to `(XR)^2=1`, and substitution of `(ETF1)`
gives `(ETF2)`.  Also

```text
R^(-1)=B^2 A X A,             T^(-4)=(A^2X)^4.
```

At their junction the three cancellations

```text
A A^2=1,             X X=1,             A A^2=1
```

give

```text
R^(-1)T^(-4)=B^2 X A^2 X A^2 X.
```

Multiplication by `RT=A^2 X A^2 B X A` proves `(ETF3)`.  Moreover
`||rho(u)-1||_2` and `||rho(v)-1||_2` are exactly the inversion and BS
covariance defects in `(R,T,X)` coordinates.

Now take the compressed even Weil tuples `phi_p` from
`sl2-half-explicit-strict-flexible-separation`.  They have dimension
`d_p=(p-1)/2`, all square-free Iwahori defects are `O(p^(-1/2))`, and they
stay a fixed distance `c_0>0` from every exact same-dimensional Iwahori
representation.  Apply `iwahori-two-triangle-torsion-normal-form`.  It
changes `(X,R,T)` by `O(p^(-1/2))`, makes

```text
X^2=(XT)^3=(XT^2R)^3=1
```

exact, and leaves inversion and BS defects `O(p^(-1/2))`.  Set
`A=XT` and `B=XT^2R`.  This is an exact representation `rho_p` of `F`, and
the preceding word computation proves `(ETF4)`.

The coordinate changes

```text
(X,R,T) -> (X,A=XT,B=XT^2R),
(X,A,B) -> (X,T=XA,R=A^2XA^2B)
```

are fixed words, hence Lipschitz in normalized Hilbert--Schmidt norm with
dimension-independent constants.  If `(ETF5)` failed along a subsequence,
the inverse word map and the `O(p^(-1/2))` normalization displacement would
put the original `phi_p` arbitrarily close to an exact same-dimensional
Iwahori tuple, contradicting its uniform strict separation.  Shrinking
`c_0` by a fixed factor proves `(ETF5)`.

Finally the uncompressed even Weil representation has dimension `d_p+1`, is
exact for the Iwahori quotient, and is at generalized flexible distance
`O(p^(-1/2))` from `phi_p`.  The additional torsion normalization movement
has the same order, so the triangle inequality proves the one-line flexible
repair assertion.
