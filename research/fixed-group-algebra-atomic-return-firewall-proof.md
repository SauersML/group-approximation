---
rg: 2
id: fixed-group-algebra-atomic-return-firewall-proof
kind: route
title: Apply cyclicity on the regular marked corner and on every exact finite packet
target: fixed-group-algebra-polynomials-cannot-supply-atomic-return
requires:
  - atomic-leavitt-gap-on-nonzero-matrix-corner
---

Let `lambda` be the left regular representation of `Gamma`.  Since `z` is a
nonidentity involution,

```text
p_lambda=(1-lambda(z))/2
```

is a nonzero projection of canonical trace `1/2`.  With normalized matrix
trace on `M_k(L(Gamma))`, the corner `P M_k(L(Gamma))P` is therefore a
nonzero finite tracial von Neumann algebra.  Normalize its trace so that
`tau_P(P)=1`.

For arbitrary `s_i,t_i` in this corner, traciality gives

```text
tau_P(t_i s_i)=tau_P(s_i t_i).                         (FGF1)
```

Hence

```text
tau_P(t_0s_0-P)+tau_P(t_1s_1-P)
  -tau_P(s_0t_0+s_1t_1-P)=-1.                         (FGF2)
```

Taking absolute values, applying the triangle inequality, and using
`|tau_P(a)|<=||a||_op` proves `(FGP3)`.  This is the same cyclic proof as
the binary case of the Atomic Leavitt Gap, and it does not require the
operators to be group-algebra elements; that restriction only makes the
regular evaluation representation-functorial.

If the four proposed formulas are fixed elements of
`P M_k(C[Gamma])P`, their left regular evaluations are covered by the
preceding calculation.  Therefore no universal identity can make all three
defects zero, and no relator-defect estimate with right side tending to zero
can hold in every exact representation: at zero defect its regular
evaluation would contradict `(FGP3)`.

For an exact finite-dimensional packet representation, replace the regular
corner by its nonzero marked spectral corner and use normalized matrix trace
there.  The identical calculation proves `(FGP3)` for arbitrary corner
operators, so a fortiori for every finite Fourier or Pauli group-algebra
polynomial.  The cited eight- and twelve-dimensional marked models therefore
give literal zero-packet-defect witnesses to the claimed scoped no-go.
