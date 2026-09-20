---
rg: 2
id: polynomial-valuation-germ-induction-preserves-marked-finiteness
kind: claim
title: Each polynomial valuation germ layer preserves F_infinity for the full group and all finite rational marked stabilizers
distinct_from:
  shell-prefix-germ-is-not-normal-or-finite-index: that excludes normality of the original cyclic prefix germ in a shell host; this requires only successive normal inclusions J_(d-1) in J_d after an affine base.
artifacts:
  - research/artifacts/polynomial-germ-unitriangular-manuscript-2026-09-20.md
---

**OPEN — substantive induction lemma, submitted proof pending independent review.**

Use `B_{d,r}` and the rational marked set `R_r` defined in artifact §§6–7.
For every `d≥1`, suppose `B_{d-1,r}` and all its finite rational marked
stabilizers have type `F_∞` for every `r≥1`. Then `B_{d,r}` and all its
finite rational marked stabilizers have type `F_∞` for every `r≥1`.
The constructed groups are countable full groups, have the stated
polynomial germs `J_d=P_d⋊Z`, and satisfy the finite-germ-extension
axioms needed in this conclusion.

## Attempts

The submitted proof uses the top Newton coefficient to identify
`J_{d-1}◁J_d` with quotient `Z`; it does not assume `J_0◁J_d`.
Belk–Hyde–Matucci 2407.03149v1 Theorem 1.1 is the explicit classical
finiteness input. To prove the stabilizer clause, fix finite `F`, set
`P=Fix_{B_{d,r}}(F)`, and let `C≤P` allow lower-relative singularities
only in `F`. The proposed exact sequence is
`1→Fix_{B_{d-1,r}}(F)→C→Z^F→1`, and fixing a further finite set `M`
replaces the kernel by `Fix_{B_{d-1,r}}(F∪M)` without changing the quotient.

Apply BHM to `C≤P` on the punctured Hausdorff space `C_r\F`; this space
is not assumed compact. Remaining tasks are to verify the actual full
group construction, exactness and surjectivity using disjoint supported
radials, all relative singularity/localization axioms after puncturing,
the oligomorphic action, and the precise theorem hypotheses for this
noncompact space. Artifact §7 records the complete proposed mechanism.
In particular the local germ groupoids of `C` and `B_{d-1,r}` must agree
away from `F`, including source/target germs. This requires lower-group
localization avoiding `F`; isotropy-germ equality alone is insufficient.
A bounded independent reading found no algebraic contradiction but did
not certify these constructions or close the claim.
