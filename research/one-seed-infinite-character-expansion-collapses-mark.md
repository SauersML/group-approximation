---
rg: 2
id: one-seed-infinite-character-expansion-collapses-mark
kind: claim
title: One seed and one infinite expanding character orbit collapse the mark outright
distinct_from:
  one-pauli-seed-character-expansion: that uses a finite character orbit and gives a dimension-or-collapse alternative; this uses an infinite nonamenable orbit and has no dimension alternative.
---

ESTABLISHED.  Let an exact elementary-abelian action on a finite-dimensional
marked carrier have spectral PVM `(P_chi)`.  Suppose all nontrivial spectral
characters which may occur lie in a countable actor-invariant set `Omega`,
and a finite symmetric actor set `S` has

```text
||M||_(ell^2(Omega)) <= 1-gamma                              (ISC1)
```

for its normalized Schreier Markov operator.  Put

```text
mu_1=sum_(chi in Omega) tr_d(P_chi),
E_act=(1/|S|) sum_s sum_(chi in Omega)
      ||C_s P_chi C_s^*-P_(s chi)||_2^2.                     (ISC2)
```

If one seed involution has anticommutation defect `eta_seed` as in `(OPS2)`,
and its negative eigenspace lies in the `Omega` spectral sum, then

```text
mu <= 2 E_act/gamma + eta_seed^2/4.                          (ISC3)
```

In particular, exact actor covariance and one exact Pauli seed force the
marked carrier to vanish in every finite-dimensional representation.

Unlike the finite-orbit theorem, no virtual size is chosen after the matrix
dimension.  A single finitely presented actor/module packet would suffice if
its nontrivial character action has the uniform infinite-orbit gap `(ISC1)`
and its word defects control `(ISC2)`.
