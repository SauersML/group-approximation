---
rg: 2
id: summable-abelian-checksum-misses-infinite-characters
kind: claim
title: A summable abelian checksum cannot resolve transport on an infinite character set
distinct_from:
  finite-covariance-energy-sees-only-character-restrictions: that gives exact collisions for a finite binary-lamp test set; this treats a countably infinite weighted library and arbitrary abelian lamps.
  bounded-hs-loss-kills-static-heavy-tail-library: that dilutes separate challenge carrier projections; this obstruction fills the entire carrier and comes from compactness of character labels.
  multiscale-square-function-checksum-forces-hs-floor: that assumes one operator defect has orthogonal decoded domains plus a backward recurrence; this proves why a norm-bounded static abelian sum cannot supply that operator.
---

ESTABLISHED.  Let `M` be any abelian group, let `(m_n)_(n>=0)` be any
sequence in `M`, and let `a_n>=0` with `sum_n a_n<infinity`.  For every
infinite character set `Omega subset hat M` and every `epsilon>0`, there are
distinct `chi,psi in Omega` such that

```text
sum_n a_n |chi(m_n)-psi(m_n)|^2 < epsilon.              (SAC1)
```

Put the two characters on equal-rank spectral subspaces of a matrix algebra,
let

```text
rho(m)=chi(m)P_chi+psi(m)P_psi,
```

and let `C` swap the two subspaces.  Then the fine spectral transport energy
for the identity actor is maximal,

```text
sum_theta ||C P_theta C^*-P_theta||_2^2=2,              (SAC2)
```

while the whole weighted covariance library satisfies

```text
sum_n a_n ||[C,rho(m_n)]||_2^2 < epsilon.               (SAC3)
```

Thus no dimension-independent inequality can bound fine character-PVM
transport by a static countable abelian test library whose total squared-HS
weight is finite.  Making the weights heavy-tailed, choosing the tests
recursively, or allowing them to separate every pair set-theoretically does
not help: an infinite subset of a compact metric label space is never
uniformly discrete.

This leaves a precise escape hatch for the recursive-checksum program.  Its
one defect cannot be a norm-convergent scalar combination of lamp covariance
tests.  It must instead use orthogonal operator domains whose energies add
inside one squared norm, together with a recurrence that promotes a deep
fine-label mismatch back to a macroscopic root signal.  That is strictly more
structure than a static heavy-tail library.
