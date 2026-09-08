---
rg: 2
id: twisted-pinch-extracts-the-coarse-prefix-receiver
kind: route
title: Round the involution, pinch the inversion intertwiner, and read the S3 multiplicities
target: frozen-cycle-extracts-a-coarse-prefix-pvm
requires: []
artifacts:
  - research/artifacts/frozen-cycle-coarse-prefix-receiver-2026-09-08.md
---

Round `J` spectrally to a self-adjoint unitary `H` at cost `s/sqrt(2)`.
The orthogonal projection onto `C T C=T` is

```text
T=(H+C H C+C^2 H C^2)/3.
```

It is self-adjoint, and
`||H-T||_2=||C H C-H||_2/sqrt(3) <= (r+sqrt(2)s)/sqrt(3)`.
Because the two nonreal `C` eigenspaces have equal dimension, a polar
completion of `T` can be chosen both self-adjoint and in the same
intertwiner space. Call it `J_0`. Polar optimality and orthogonality
give `||J_0-H||_2 <= sqrt(2)||H-T||_2`, proving the stated bound.

The exact pair `J_0,C` represents `S_3`. If the trivial, sign and
standard multiplicities are `a,b,t`, the frozen cycle profile gives
`t=m` and `a+b=m`. This is the induced representation from the
stabilizer of one of three letters with fiber representation
`a` trivial plus `b` sign copies. Its three coset cells give the
required equal-rank PVM.

For projections `P,Q`, normalized HS distance squared is at least
the absolute difference of their normalized ranks. Each conjugate of
`Q_01` has rank `m`, whereas the two target child ranks sum to `m`.
Adding the two rank bounds gives `1/3`. The artifact checks the
six-point sharpness example and the exact native transport orientation.

For the source-authenticated boundary, map `c` to the coordinate
three-cycle in `GL_3(F_2)` and all three `b_i` to `x_12(1)`, giving
`b_2,b_3` distinct central `C_2` tags. The regular representation
has both frozen finite-factor profiles. The artifact evaluates every
shared compiler word: `X_0=X_1=(23)`, so `B=I`, and only the retained
rows `rho_5=D,rho_8=c` fail. Orthogonality of `Q_01` and `Q_1`
makes the two child squared errors sum to one for every refinement.

The conclusion concerns an auxiliary anchor and projection receiver.
It supplies no correction of the original finite-factor generators,
and no proof that the remaining packet relators produce that receiver.
