---
rg: 2
id: affine-s3-endpoint-permutes-active-atoms
kind: claim
title: The affine stabilizer of the forbidden endpoint is an S3 permuting the three active atoms
distinct_from:
  six-generator-one-jump-router-has-s3-radical-atlas: that S3 permutes the three radical endpoint charts while fixing K; this is a different affine S3 on one fixed marked (K,b) character square, and it permutes the three active atoms themselves.
  s3-active-vector-carries-positive-density-multiplicity-algebra: that uses the full D-commutant of three unrelated atom spaces; this finite overgroup forces equal atom ranks and supplies an invariant positive-density algebra.
---

Let

```text
D=<J,K,b>~=(C_2)^3,
Q=(1-J)/2,        P_(epsilon,delta)=Q(1+epsilon K)(1+delta b)/4,
A=P_(+,+)+P_(+,-)+P_(-,+),          X=P_(-,-).          (ASE1)
```

There are two automorphisms of `D`, fixing `J`, given by

```text
s: K |-> K,       b |-> J K b,
u: K |-> J K b,   b |-> b.                              (ASE2)
```

They satisfy `s^2=u^2=(su)^3=1`.  On the marked `J=-1` character
square they fix the forbidden character `(K,b)=(-1,-1)` and generate its
full affine stabilizer, hence an `S_3` acting transitively on the other three
characters.  Put

```text
C_aff=D semidirect <s,u> ~= D semidirect S_3.             (ASE3)
```

In every exact finite-dimensional representation of `C_aff`, the three
active atom ranks are equal.  If their sum has normalized Hilbert mass `a`
inside an ambient `d`-dimensional representation, then the commutant of
`C_aff` on the active carrier has normalized adjoint density at least

```text
dim End_(C_aff)(A C^d)/d^2 >= a^2/18.                    (ASE4)
```

The affine group may be attached to the six-generator packet by the finite
amalgam

```text
G_aff=B *_D C_aff.                                       (ASE5)
```

Normal form embeds `B`, so `J` remains nontrivial.  Moreover every exact
`J=-1` representation of `B` has an induced (generally infinite-dimensional)
representation of `G_aff` on which `J=-1`.  Thus the affine equalizer is
compatible with the properly infinite completeness convention; it does not
assume that an arbitrary finite-dimensional packet representation already
has equal active multiplicities.

After fixed-table Hilbert--Schmidt exactification, `(ASE4)` persists with an
`O(sqrt(E))` loss in `a`.  This is a local finite-group theorem.  It still
does not put the resulting algebra in the commutant of an independent
Toeplitz/property-`(T)` coefficient factor.
