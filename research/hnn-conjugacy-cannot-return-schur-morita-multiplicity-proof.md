---
rg: 2
id: hnn-conjugacy-cannot-return-schur-morita-multiplicity-proof
kind: route
title: Unitary equivalence preserves every finite-group isotypic multiplicity
target: hnn-conjugacy-cannot-return-schur-morita-multiplicity
requires:
  - predicate-rank-gate-doubles-restriction-multiplicity
---

If `phi:H_1->H_2` is the subgroup isomorphism used by an HNN edge and a
representation `rho` satisfies

```text
rho(s)rho(h)rho(s)^*=rho(phi(h)),
```

then `rho|H_1` and `rho|H_2 o phi` are unitarily equivalent. Their character
inner products, hence every irreducible multiplicity and weighted
multiplicity, are identical.

On an active Schur sector, restriction from `B_f` to `A_f` changes the
baseline multiplicity from `m` to `2m` by `(HCM1)`. No unitary equivalence can
identify that output with a next input having multiplicity `m`. Attempting to
conjugate the complete finite tables also forces the represented image groups
to be isomorphic and gives the same conclusion even when the representation
has a kernel. Thus plain HNN/Bass--Serre transport cannot be the missing
Morita return.
