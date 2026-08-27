---
rg: 2
id: atlas-first-composable-mixed-pair-zero-rank-proof
kind: route
title: Keep both St3 product paths and compute the first composable quotient matrix
target: atlas-first-composable-mixed-pair-has-zero-quotient-rank
requires: []
---

The MSI audit identifies the first two mixed-direction nonconstant St3 rows
and their sparse word sizes. In the rectangular model, the common first leg
is `A:V_3->V_1`, the two second legs are arbitrary
`B_j:V_2->V_3`, and the RHS occurrences are `C_j=AB_j`. Block
multiplication proves both St3 relations exactly.

After the two desired product columns and two RHS nuisance columns are
listed honestly, the scalar coefficient matrix is `[I_2,-I_2]`. Its rank
equals the nuisance rank, so the quotient-rank increment is zero by
`atlas-mixed-minor-needs-nuisance-quotient-rank`. This is the promised exact
rectangular countermodel for the first composable family.
