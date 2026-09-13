---
rg: 2
id: fpbs-pivotal-volume-defect-criterion-proof
kind: route
title: Stabilize along one finite path and isolate the nonnegative excess in expectation
target: fpbs-pivotal-volume-defect-criterion
requires:
  - fpbs-global-pivotal-tail-at-uniqueness
artifacts:
  - research/artifacts/fpbs/docs/global-pivotal-tails-and-volume-defect.md
---

Artifact Section 4 proves the deterministic statement: after a fixed
finite open v-to-w path enters V_R, every finite-volume pivotal lies
on that path. Each edge on the path which is not globally pivotal has
a finite open bypass. Once the finitely many bypasses also enter V_R,
the finite and global pivotal sets agree. On E_R every global pivotal
is already a finite-volume pivotal, proving nonnegativity throughout.

The required tail theorem gives integrability of Z. Thus
E[Z 1_(E_R)] tends to E Z while P(E_R) tends to P(E)>0. Divide
E Z_R=E[Z 1_(E_R)]+E B_R by P(E_R). Convergence of conditional
means is exactly E B_R tending to zero. Since B_R tends almost surely
to zero and is nonnegative, this is equivalent to uniform
integrability. The difference Z_R-B_R is dominated by integrable Z,
so uniform integrability of Z_R and of B_R is equivalent. Section 5
justifies averaging over the finite-support endpoint X_n at fixed n.
