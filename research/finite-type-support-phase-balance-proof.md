---
rg: 2
id: finite-type-support-phase-balance-proof
kind: route
title: Compare every group coefficient in a finite-type partition
target: finite-type-partitions-obey-support-phase-balance
requires: []
---

For a finite subgroup `H` and `rho in Irr(H)`, the primitive central
idempotent is

```text
z_(H,rho)=d_rho/|H| sum_(h in H) chi_rho(h^(-1)) h.
```

Conjugating transports both the subgroup and the character, so the
coefficient of `s` in `p_a` is exactly `c_a(s)` from `(SPB1)`. The
group elements are a linear basis of `C[Gamma]`. Comparing their
coefficients in `sum_a p_a=q` gives `(SPB4)` immediately, including zero
on every `s notin K`.

Taking the identity coefficient gives

```text
sum_a d_a/|A_a| chi_(rho_a)(1)
 =d_pi/|K| chi_pi(1),
```

which is `(SPB3)` because `chi_rho(1)=d_rho`.

Now fix `s notin K`. Equation `(SPB4)` says that the incident nonzero
complex numbers `c_a(s)` sum to zero. There cannot be exactly one. If there
are exactly two, their sum is zero, proving `(SPB5)` and equality of their
moduli. Dividing their zero sum by the number of incident atoms puts zero in
their convex hull. If they all lie in one open half-plane through the
origin, multiplication by a common phase makes all of their real parts
strictly positive, contradicting zero sum.

If all escaped coefficients are nonnegative real, their zero sum forces
every one to be zero. Thus the Fourier support of every `p_a` is contained
in `K`, so `p_a in C[K]`. From `(SPB2)`, `p_a<=q`, whence

```text
p_a=q p_a q in q C[K] q.
```

The latter is finite-dimensional. This proves the positive-character
boundary and all claimed support consequences. Notice that orthogonality is
needed to interpret the family as a context PVM and to obtain `p_a<=q`;
the coefficient balance itself follows from the additive equality alone.
