---
rg: 2
id: pure-mf-conventions-imply-sofic-proof
kind: route
title: Reduced-norm convergence at g minus one separates points, then Mal'cev
target: pure-mf-conventions-imply-sofic
requires: []
artifacts:
  - GroupApproximation/Sofic/MFRepresentationVariants.lean
---

## Direct proof

Let `pi_n : G -> U(d_n)` be the genuine representations of a PMatF
approximation (`PurelyMatricialFieldApproximation`, whose field
`reducedNormConverges` quantifies over every finitely supported `c : G ->0 C`).

**Points are separated.**  Let `g != 1`.  The left regular representation is
faithful, so `lambda(g) != 1` and `||lambda(g) - 1|| > 0`.  Applying norm
convergence to `c = delta_g - delta_1` gives

```text
||pi_n(g) - 1|| -> ||lambda(g) - 1|| > 0,
```

so `pi_n(g) != 1` for all large `n`.

**Finitely generated subgroups are residually finite.**  Let `H <= G` be
finitely generated and `h != 1` in `H`.  Choose `n` with `pi_n(h) != 1`.  The
image `pi_n(H)` is a finitely generated subgroup of `GL_(d_n)(C)`, so it is
residually finite by Mal'cev's theorem.  A finite quotient of `pi_n(H)` not
killing `pi_n(h)`, composed with `pi_n`, is a finite quotient of `H` not killing
`h`.

**Soficity.**  Residually finite groups are sofic, and soficity is local, so
`G` is sofic.

**The other conventions.**  The formal implications
`IsPurelyPermutationField.isPurelyMatricialField`, `IsPPF.isPFF`,
`IsPFF.isTracePMF` and `IsTracePMF.isPurelyMatricialField` in the cited Lean
file reduce trace-free PPermF, PPF, PFF and trace-PMF to PMatF.

Not formalized here: Mal'cev's theorem and the locality of soficity; both are
standard.
