---
rg: 2
id: select-one-irreducible-summand-from-the-full-support-soft-packet
kind: route
title: Minimize the combined Rayleigh quotient across irreducible summands
target: native-relator-soft-modes-persist-in-simple-ideal-blocks
requires:
  - km-triangle-relative-gap-failure-has-fd-full-support-witnesses
---

Apply `(FDR2)--(FDR5)` with tolerances small enough that one finite-dimensional
representation `sigma` and one unit vector `v` satisfy

```text
H_sigma^K={0},
sum_(g in F)||sigma(g)v-v||^2
 +sum_(x in B_W)||sigma(x)v||^2<eta.                       (1)
```

Decompose the finite-dimensional representation into irreducibles,

```text
sigma=direct_sum_i rho_i,       v=direct_sum_i v_i.
```

For every `i` with `v_i!=0`, set `xi_i=v_i/||v_i||` and let `E_i` be the
left side of `(NSB1)` for `(rho_i,xi_i)`.  Orthogonality of the summands gives

```text
sum_i ||v_i||^2 E_i<eta,       sum_i||v_i||^2=1.           (2)
```

Hence some `i` has `E_i<eta`.  Choose that irreducible summand and write it as
`rho`.

It remains to identify its ideal image.  Since `H_sigma^K={0}`, no irreducible
summand is trivial on `K`.  Therefore `rho(I)` is a nonzero two-sided ideal of
the simple matrix algebra `rho(A)=M_d`; irreducibility gives the last equality
by Burnside.  It follows that

```text
rho(I)=M_d
```

and its support projection is the identity.  This proves `(NSB1)--(NSB2)`.
Letting `eta` tend to zero with `F` empty refutes every proposed positive
constant in `(NSB3)`.
