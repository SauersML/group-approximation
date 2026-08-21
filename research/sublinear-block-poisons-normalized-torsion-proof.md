---
rg: 2
id: sublinear-block-poisons-normalized-torsion-proof
kind: route
title: Compute direct-sum weights and tune a vanishing corner near singularity
target: sublinear-block-poisons-normalized-torsion
requires: []
---

Word traces and squared Hilbert--Schmidt defects are normalized direct-sum
averages, which gives the two displayed formulas and proves that `Z_n` has the
same limiting moments and defects as `V_n`.

For a fixed square polynomial `P`, determinant multiplicativity gives

```text
ell_(d_n+r_n)(P(Z_n))
 = d_n/(d_n+r_n) ell_(d_n)(P(V_n))
 + r_n/(d_n+r_n) ell_(r_n)(P(W_n)).
```

Choose a fixed-size or sublinear block family approaching a singular
evaluation, and tune its smallest singular value so that the second term has
any prescribed finite negative size or diverges. Relator defects on that block
may remain bounded away from zero: their global contribution is only
`O(r_n/d_n)`. The same calculation applies term by term to a finite based
complex's normalized torsion.

Finally, Fuglede--Kadison determinant itself is multiplicative and invariant
under unitary conjugacy and stabilization. Therefore identities justified only
by those formal operations persist in the regular von Neumann algebra and
cannot separate finite matrices from the canonical group trace.
