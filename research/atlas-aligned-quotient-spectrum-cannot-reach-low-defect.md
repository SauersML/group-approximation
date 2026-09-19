---
rg: 2
id: atlas-aligned-quotient-spectrum-cannot-reach-low-defect
kind: claim
title: The aligned quotient spectrum is multiplicity-uniform but cannot reach the low-defect branch
distinct_from:
  atlas-aligned-word-jacobian-has-full-multiplicity-absorber: that identifies the full multiplicity kernel before quotienting; this computes what remains after quotienting and compares its domain of validity with the actual 19243 distance wall.
  atlas-19243-centrality-forces-s3-distance: that proves low-defect frames stay far from the S3 commutant; this shows why that fact makes every aligned transverse Hessian irrelevant even when its quotient spectrum has a uniform gap.
  atlas-fold-localization-with-uniform-remainder: that asks low-defect frames to approach the classical fold and is open; this proves the opposite fixed-distance wall for the actual centrality consequence and redirects the quotient invariant to a remote nonlinear branch.
---

**ESTABLISHED LOCAL-QUOTIENT FIREWALL.**  Let `F` be the actual map formed
by the five saturated boundary words and the centrality word `c_19243`, and
let `U_0` be any exact aligned regular-chart frame.  After quotienting the
right- and left-commutant orbit tangents, every nonzero singular value of
`dF_(U_0)` belongs to a fixed finite list depending only on pairs of complex
irreducible `A8` representations.  In particular its least positive
singular value, if one is selected, is independent of external multiplicity
`k`.

This uniform local spectrum cannot control a low-packet-defect sequence.
The aligned orbit is contained in the commutant of the collision subgroup
`K_19243 ~= S3`.  By
`atlas-19243-centrality-forces-s3-distance`, every frame `U` satisfies

```text
dist_2(U,C_K)
 >=max(0,(sqrt(2)-||pi_U(c_19243)-1||_2)/16).         (AQS1)
```

Consequently any sequence on which the actual packet defect tends to zero
obeys

```text
liminf dist_2(U,C_K)>=sqrt(2)/16,                     (AQS2)
```

and hence stays at least that far from every aligned double-commutant orbit.
No inverse-function, Hessian, or smallest-transverse-singular-value estimate
on a fixed neighborhood of the aligned quotient can apply to such a
sequence.

Thus quotienting the exact gauge does remove the artificial multiplicity
zero modes, but it does **not** expose the missing Atlas obstruction.  The
only surviving transverse-singular target is global: construct a uniformly
coercive invariant on the macroscopically remote nonlinear branch singled
out by `(AQS2)`.  A finite irrep-pair Hessian calculation at the classical
fold, regardless of how favorable its smallest positive eigenvalue is,
cannot establish the five-row lift.

