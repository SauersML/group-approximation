---
rg: 2
id: fournier-facio-compression-coset-charge-proof
kind: route
title: Inject the infinite simple defect into the coset space and push every charge down
target: fournier-facio-compression-coset-charge-impossible
requires:
  - fournier-facio-torsion-free-skeleton
  - no-invariant-mean-on-coset-space
---

The skeleton gives an infinite subgroup `J` with

```text
[Gamma,J]=1,                 Gamma cap J=1.
```

It is infinite because it is conjugate to the nontrivial torsion-free simple
group `pi(S)`.  The map

```text
J -> G/Gamma,                j |-> j Gamma
```

is injective: equality of two cosets puts `j_2^-1 j_1` in
`Gamma cap J`.  Thus `[G:Gamma]=infinity`.  Since `G` has property `(T)`, the
established non-coamenability theorem forbids a `G`-invariant mean on
`G/Gamma`.

For the fibred statement define

```text
bar_mu(A)=mu(p^-1(A)).
```

Finite additivity and normalization are immediate.  Invariance of `mu` and
the conull equivariance of `p` give `bar_mu(gA)=bar_mu(A)` for every `g`, a
contradiction.  The argument is unchanged for an ultrafilter or Banach-limit
charge.

