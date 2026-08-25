---
rg: 2
id: kt-full-kazhdan-majorana-return-fd-proof
kind: route
title: Combine finite-image compression collapse with the adjoint Kazhdan gap
target: kt-full-kazhdan-majorana-return-collapses-in-fd
requires:
  - fd-invisibility-of-compression
  - kt-elementary-kazhdan-packet-rounds-base-lamp
  - kt-ab-marked-return-is-the-first-mixed-cylinder
---

Write `E=EL_3(F_2[x_1^(+-1),x_2^(+-1),x_3^(+-1)])` and let
`Lambda<Gamma` be any of the positive compressed elementary subgroups used
in the Kun--Thom pair.  Restrict a genuine finite-dimensional
representation `rho:G->U(D)` to `E`.  By
`fd-invisibility-of-compression`,

```text
rho(E)=rho(Lambda) <= rho(Gamma).                           (FKM4)
```

The explicit element `h` in `(FKM1)` belongs to `E`, hence
`rho(h) in rho(Gamma)`.

Let `P_Gamma` be the orthogonal projection of normalized Hilbert--Schmidt
space `L^2(M_D)` onto `rho(Gamma)'`.  Apply the Kazhdan inequality for the
adjoint representation and the generating packet `K`:

```text
||X-P_Gamma(X)||_2
 <= kappa_K^(-1) max_(s in K)||[X,rho(s)]||_2.              (FKM5)
```

Since `rho(h) in rho(Gamma)`, the element `P_Gamma(X)` commutes with
`rho(h)`.  The commutator with a unitary has `2`-norm at most twice the
distance from a commuting element, so `(FKM5)` gives `(FKM2)`.

Now take `c=c*=c^(-1)` and put `d=rho(h)c rho(h)^*`.  Unitary invariance
and `(FKM2)` give

```text
||d-c||_2=||[c,rho(h)]||_2 <= (2/kappa_K)delta_K.           (FKM6)
```

Using `c^2=1`,

```text
cd+dc-2 = c(d-c)+(d-c)c,
```

so its norm is at most `2||d-c||_2`.  The reverse triangle inequality and
`||2I||_2=2` prove `(FKM3)`.

For the finite-quotient interpretation, if `theta:G->F` is any finite
quotient, `(FKM4)` says `theta(h) in theta(Gamma)`, and `K` generates
`Gamma`.  Hence the cosets fixed by `theta(K)` are also fixed by `theta(h)`.
The two supposed Clifford labels in the one-root construction coincide;
the anticommutation relation is precisely the relation that fails.
