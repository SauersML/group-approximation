---
rg: 2
id: vn-rank-galois-invariant-for-torsion-free-groups
kind: claim
title: Von Neumann kernel dimensions over torsion-free groups are invariant under field automorphisms of C fixing the algebraic numbers
distinct_from:
  strong-atiyah-base-change-algebraic-to-complex: that is the implication from algebraic to complex Strong Atiyah; this is the rank-invariance input that makes one proof of it work, and asserts no integrality.
---

**OPEN.**  For every torsion-free group `H`, every `A in M_(m,n)(C[H])` and
every field automorphism `sigma` of `C` fixing `Qbar` (in general
discontinuous),

```text
dim_(N(H)) ker r_(sigma(A)) = dim_(N(H)) ker r_A,
```

where `sigma(A)` applies `sigma` to every coefficient.  The property passes to
subgroups, since kernel dimensions of matrices over `C[K]`, `K <= H`, agree
over `N(K)` and `N(H)` (Step 1 of `algebraic-atiyah-determinant-colimit-proof`).

## Attempts

* **Sofic groups.**  The sofic Lueck approximation theorem (Jaikin-Zapirain,
  GAFA 29 (2019), Theorem 1.3, quoted as Theorem 2.1 of arXiv:2201.03268)
  writes the rank as a limit of normalized ranks of complex matrices.  The rank
  of a complex matrix is fixed by every field automorphism, so invariance holds
  for sofic groups.  It does not extend to all torsion-free groups:
  `galois-invariance-via-sofic-luck-approximation` is dead.
* **From integrality.**  Integer-valued rank functions on `C[H]` need not be
  unique, so Strong Atiyah over `C` does not by itself give invariance.
