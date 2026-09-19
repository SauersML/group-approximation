---
rg: 2
id: paired-finite-group-intertwiner-laplacian-proof
kind: route
title: Regard every relation pair as a generator of a finite product subgroup
target: paired-finite-group-intertwiner-laplacian
requires:
  - finite-group-intertwiner-laplacian-gap
  - finite-group-intertwiner-shrinkage-formula
---

Define two unitary representations of the finite group `K` by

```text
rho_K   = rho o p_1,
sigma_K = sigma o p_2.
```

For a generating pair `k_s=(a_s,b_s)` of `K`, the ordinary intertwiner defect
is exactly

```text
||rho_K(k_s)T-T sigma_K(k_s)||_2
 = ||rho(a_s)T-T sigma(b_s)||_2.
```

Therefore `(PFGI1)` is precisely the standard intertwiner Laplacian of the two
`K`-representations on the displayed generating set.  A vector has zero energy
if and only if it intertwines all generators, hence all of `K`, proving
`(PFGI2)`.

Apply `finite-group-intertwiner-laplacian-gap` to `K`: the positive spectrum
away from `Hom_K(sigma_K,rho_K)` has a gap determined by the finitely many
irreducible `K`-pair blocks.  Amplifying fixed representation types merely
repeats those blocks, so it does not change the gap.

Finally apply `finite-group-intertwiner-shrinkage-formula` to the same exact
`K`-intertwiner matrix space.  This gives `(PFGI3)` from the two isotypic
multiplicity vectors.
