---
rg: 2
id: tracial-support-affine-linearization-proof
kind: route
title: Joint spectral support proves the affine LCS relaxation
target: tracial-support-affine-linearization
requires: []
artifacts:
  - research/artifacts/lcs-exact-support-sparsification-2026-08-18.md
---

In the tracial GNS representation, a projection of trace zero has 2-norm zero
and hence is the zero operator.  Thus for each constraint the nonzero joint
spectral projections occur only at assignments in `S_i`.

An affine subset of `F_2^{V_i}` is the common zero set of finitely many affine
linear forms.  If

```text
sum_(v in V_i) c_v a_v = b
```

holds for every `a in A_i=Aff(S_i)`, then it holds in particular on every
nonzero spectral outcome.  Evaluating the corresponding parity word in the
commuting involutions and expanding against the joint PVM therefore gives the
scalar `(-1)^b` on every nonzero block, hence the exact operator identity.
Applying this to a basis of the affine equations defining every `A_i` produces
a finite LCS satisfied by the original tracial representation.
