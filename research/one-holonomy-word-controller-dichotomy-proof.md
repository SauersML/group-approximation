---
rg: 2
id: one-holonomy-word-controller-dichotomy-proof
kind: route
title: Read controller relators as exponent equations in the return holonomy
target: one-holonomy-word-controllers-are-free-or-torsion
requires:
  - verifier-controlled-two-cycle-is-existentially-loss-blind
---

Tensor factors commute, so multiplying `(OH1)` proves `(OH2)`, with
`n_rho` the signed exponent sum and `F_rho` the corresponding flag word.
The relator equation is

```text
F_rho tensor A^(n_rho)=1.                                  (OHP1)
```

Equality of a simple tensor with the identity forces both factors to be
scalar inverses.  If `n_rho=0`, exact solvability therefore requires
`F_rho=1`.  If every exponent is zero, `(OHP1)` contains no `A`, proving the
free branch and allowing the cyclic shifts from `(VTL7)`.

If some `n=n_rho` is nonzero, write `F_rho=lambda 1`.  Because `F_rho` lies
in a representation of the finite packet of exponent `e`, `lambda^e=1`.
Raising `(OHP1)` to the `e`-th power gives `A^(ne)=1`; replacing the exponent
by its absolute value proves `(OH3)`.  Additional relators can only lower the
bounded projective order.

Finally suppose `(OH4)` holds with nonzero

```text
q=sum_(g in T) c_g g in C[Gamma]
```

and finite support `T`.  Equality says that left multiplication by `w^(2N)`
preserves the finite coefficient-labelled support of `q`.  Hence some positive
power of that permutation fixes an element `g in T`, giving
`w^(2Nk)g=g` and therefore `w^(2Nk)=1`.  This contradicts infinite order.
Thus `(OH4)` forces `q=0` for a wandering `w`.

