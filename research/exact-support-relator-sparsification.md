---
rg: 2
id: exact-support-relator-sparsification
kind: claim
title: An exact-support mass gap sparsifies to a finitely presented nonhyperlinear group
artifacts:
  - research/artifacts/lcs-exact-support-sparsification-2026-08-18.md
---

Let `S` be a finite relator menu in a finitely generated free group, `j` a
marked word, and `mu` a probability distribution on `S`.  Suppose there is a
tracial unitary assignment `rho` with

```text
d_2(rho(j),1) >= delta0 > 0
```

and let

```text
E = {r in S : rho(r)=1 exactly},
g = mu(E).
```

Fix `0<delta<delta0`, `0<eps<eps_plus`, and use the compact finite trace-profile
space of `finite-trace-profile-net-is-dimension-free` for

```text
W = S union {j}.
```

For `delta`-marked finite-dimensional profiles `z`, put

```text
p(z) = Pr_(r~mu)[2-2 z_r <= eps_plus^2],
q = sup_z p(z).
```

If

```text
g > q,
```

then there is a finite multiset `T` of relators from `S` such that the
presentation `Gamma_T=<generators | T>` has `j != 1` but `j` is trivial in
approximate representations.  In particular `Gamma_T` is finitely presented
and nonhyperlinear.

The point is that the **whole** menu need not have perfect tracial
completeness.  It is enough for the mass of checks satisfied exactly by one
tracial representation to exceed the maximum enlarged-threshold satisfaction
mass of any marked finite-dimensional approximate assignment.
