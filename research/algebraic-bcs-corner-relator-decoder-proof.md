---
rg: 2
id: algebraic-bcs-corner-relator-decoder-proof
kind: route
title: Give every finite corner identity a van Kampen certificate and round once on the retained carrier
target: algebraic-bcs-corner-has-relator-energy-decoder
requires:
  - non-ce-bcs-has-robust-approximate-energy-gap
  - bcs-corner-model-is-a-compatible-projection-atlas
  - embedded-packet-projection-has-no-relator-ideal-certificate
---

Write

```text
b_x=Phi(X_x) in q C[Gamma]q.
```

The finite list of algebraic identities

```text
q*=q, q^2=q,
b_x*=b_x, qb_x=b_x=b_xq, b_x^2=q,
[b_x,b_y]=0 inside every context,
and every ordered forbidden product equals zero          (ARD1)
```

holds in `C[Gamma]`.  Expand each left side as a finite sum of free-group
words.  Group equal terms by their image in `Gamma`.  The coefficient sum in
every group-element class is zero.  Choosing one representative word in each
class writes the expression as a finite linear combination of differences

```text
w-w_0=(w w_0^-1-1)w_0,             w w_0^-1=1 in Gamma. (ARD2)
```

Every one of the finitely many null words in `(ARD2)` has a finite van Kampen
proof using a finite subset `R_0 subset R`.  Telescoping those proofs and
using the fixed l1 norms of the coefficient expressions gives one constant
`C_0` such that evaluation at any unitary tuple obeys

```text
sum_(f in (ARD1)) ||f(U)||_2^2 <= C_0 epsilon(U)^2.      (ARD3)
```

This is the ordinary-word payment step; it uses no stability theorem.

Choose the group-algebra expression for `q` selfadjoint.  From `(ARD3)`, the
selfadjoint matrix `q(U)` has small idempotent defect.  Scalar spectral
rounding at `1/2` gives a projection `Q` with

```text
||Q-q(U)||_2 <= 2||q(U)^2-q(U)||_2.                     (ARD4)
```

All coefficient evaluations have fixed operator-norm bounds given by their
finite l1 coefficients.  Hence `(ARD3)--(ARD4)` show that
`C_x=Qb_x(U)Q` is selfadjoint and has `||C_x^2-Q||_2=O(epsilon)`.
Reflection rounding inside `Q` gives a selfadjoint unitary `Z_x` with

```text
||Z_x-C_x||_2=O(epsilon).                               (ARD5)
```

The fixed commutator and forbidden-product polynomials are Lipschitz on this
uniformly bounded finite tuple.  Combining `(ARD3)` and `(ARD5)`, then
renormalizing the Hilbert--Schmidt norm on `Q C^d`, proves

```text
E_B(Z)<=C epsilon(U)^2/tau(Q),                           (ARD6)
```

for one dimension-independent `C`.  Under `(ARC3)`, this is `(ARC4)`.
The robust non-CE BCS gap gives `E_B(Z)>=beta_B^rob`, proving `(ARC5)`.

Finally, canonical moment convergence gives
`tau(q(U))->tau_Gamma(q)>0`; `(ARD4)` gives the same limit for `tau(Q)`.
Thus canonical microstates eventually meet `(ARC3)`.  Conversely, without
the algebraic zero identities `(ARD1)`, a positive packet energy cannot be
bounded by relator defects: the left regular representation is the exact
countermodel recorded by
`embedded-packet-projection-has-no-relator-ideal-certificate`.

