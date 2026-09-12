---
rg: 2
id: relation-centralized-adjoint-density-dichotomy-proof
kind: route
title: Compute diagonal central-character collision mass and pass to Haar measure
target: centralized-quotient-shadow-density-dichotomy
requires: []
---

For `a in A`, conjugation by `pi(a)` acts on
`Hom(H_chi,H_psi)` by the scalar `psi(a)chi(a)^(-1)`.  It is trivial for
every `a` exactly when the two characters agree, proving `(RCQ3)` and
`(RCQ4)`.

Canonical trace convergence on the central subgroup is weak convergence of
the finite spectral measures to Haar measure on its compact dual.  If the
image is infinite, Haar measure has no atoms.  Were some atom of the finite
measures to retain weight at least `epsilon`, compactness would give a
convergent subnet of its locations and the Portmanteau inequality would put
an atom of weight at least `epsilon` in the Haar limit.  Hence the maximal
weight tends to zero, and

```text
sum p_chi^2 <=max p_chi sum p_chi=max p_chi ->0.
```

If the central image and the quotient by it are finite, the base image is
finite.  Conjugation preserves subgroup cardinality, so an inclusion of a
conjugate copy into that finite base is equality.  This proves `(RCQ6)`.
