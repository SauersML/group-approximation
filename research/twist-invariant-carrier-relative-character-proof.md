---
rg: 2
id: twist-invariant-carrier-relative-character-proof
kind: route
title: Subtract two scalar-twisted return estimates on the identical carrier
target: twist-invariant-carriers-force-relative-character-kernels
requires: []
---

For every word `g`, scalar centrality gives the exact identity

```text
g(U^chi)=chi(g)g(U).                                    (TIC7)
```

In particular, putting `V=w(U)` and `z=chi(w)`, the two inequalities in
`(TIC3)` are

```text
||(V-1)X_U||_2<=epsilon,
||(zV-1)X_U||_2<=epsilon.
```

Subtract their left-hand operators before taking norms.  Since `V` is
unitary,

```text
|z-1| ||X_U||_2
 =||(z-1)VX_U||_2
 <=||(zV-1)X_U||_2+||(V-1)X_U||_2
 <=2epsilon.
```

This is `(TIC4)`.

Every defining relator has trivial image under a character of `Gamma`, so
twisting does not change any relator defect.  Equation `(TIC6)` proves that
canonical-profile convergence is also preserved.  Because `chi|H=1`, the
two microstates have identical restrictions to `H`; hence any exactification
and carrier rule depending only on that restriction gives the same `X_U`.
If `||X_U||_2^2>=alpha-o(1)` and `epsilon=o(1)`, `(TIC4)` contradicts
`chi(w)!=1`.

Circle-valued characters separate points of every discrete abelian group
(`T` is an injective cogenerator).  Hence the intersection of the kernels of
all characters of `Gamma` trivial on `H` is exactly
`normalClosure(H)[Gamma,Gamma]`.  For the free bridge coordinates used in the
Fanizza HNN/covariance cells, the evident exponent map to `Z` already shows
that zero free bridge exponent is necessary.
