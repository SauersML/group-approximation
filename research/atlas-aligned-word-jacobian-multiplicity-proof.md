---
rg: 2
id: atlas-aligned-word-jacobian-multiplicity-proof
kind: route
title: Split every aligned word derivative into representation and multiplicity factors
target: atlas-aligned-word-jacobian-has-full-multiplicity-absorber
requires:
  - atlas-a4-context-exact-regular-normalization
  - atlas-phase-jacobian-has-invertible-gauge-kernel
---

Put

```text
H=direct_sum_sigma V_sigma tensor M_sigma,
rho(g)=direct_sum_sigma sigma(g) tensor I_(M_sigma).
```

At an aligned frame, every prefix and suffix occurring in the derivative of
an alternating two-chart word is a matrix from one of the two aligned
regular copies.  After left trivialization, the derivative is therefore a
finite sum of maps

```text
X |-> rho(g) X rho(h).
```

On the rectangular summand

```text
Hom(V_sigma,V_tau) tensor Hom(M_sigma,M_tau)
```

such a map is

```text
[A |-> tau(g) A sigma(h)] tensor I_(Hom(M_sigma,M_tau)).
```

Finite sums, stacking several word derivatives, and taking their joint
kernel preserve this tensor factorization.  This proves `(AJM1)`.

The common scalar rotation `U(t)=exp(it)U_0` changes no conjugated second
chart letter, so every word evaluation is constant in `t`.  Its tangent
`iU_0` is therefore in the joint kernel.  Since `U_0` aligns the regular
copies, its nonzero `(alpha sigma,sigma)` block is

```text
A_sigma tensor B_sigma
```

with `A_sigma` invertible and `B_sigma` unitary.  By `(AJM1)`,

```text
0=D_W^(alpha sigma,sigma)(A_sigma) tensor B_sigma.
```

As `B_sigma` is nonzero, `D_W^(alpha sigma,sigma)(A_sigma)=0`.  Tensoring
with an arbitrary multiplicity matrix proves `(AJM3)`.

Now compress by minimal Fourier projections.  On multiplicity spaces,

```text
q_(alpha sigma,b)(A_sigma tensor B)p_(sigma,a)
  =(A_sigma)_(b,a) B.                                      (AJM5)
```

If the displayed scalar is nonzero, arbitrary `B` sends an arbitrary
nonzero source multiplicity vector to any prescribed target multiplicity
vector.  The collective range is therefore the whole target minimal block,
which proves `(AJM4)`.

Finally, the nonzero coefficient graph of an invertible matrix has Hall's
property: if a set of columns had fewer neighboring rows, those columns
would be linearly dependent.  Block by block, the support of `U_0` therefore
carries all source rank to equal target rank.  Since this support is included
in the collective-range graph of the joint kernel, no Hall deficit is
possible there.  This proves the final assertion.

