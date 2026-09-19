---
rg: 2
id: finite-tracial-one-cut-balance
kind: claim
title: A unitary has equal Hilbert-Schmidt leakage across the two directions of a finite projection cut
artifacts:
  - notes/ATLAS_RELATIVE_PERFECTNESS_AND_COEFFICIENT_ENDPOINT.md
---

Let `(M,tau)` be a finite tracial von Neumann algebra, let `P in M` be a
projection and `W in M` a unitary.  Then

```text
||(1-P) W P||_2 = ||P W (1-P)||_2.                    (CUT)
```

The statement is dimension-free and remains true in matrix amplifications.
It is useful as a finite-multiplicity obstruction: an approximately one-sided
triangular unitary cannot carry a fixed positive amount of mass in the
opposite off-diagonal corner.