---
rg: 2
id: atlas-first-two-mixed-rows-zero-rank-proof
kind: route
title: Evaluate the first shared-occurrence mixed pair on arbitrary rectangular coefficient maps
target: atlas-first-two-mixed-rows-have-zero-reservoir-rank
requires: []
---

The MSI audit identifies the first two rows and checks their word sizes. For
the proof, the shared root `x_12(e)` is `1+N` with
`N=iota_1 a p_2`, while the two fine roots are `1+M_j` with
`M_j=iota_3 b_j p_2`. The root-index equations give `NM_j=M_jN=0`
for both `j`, without using any relation among `a,b_0,b_1`. Hence both
relators vanish simultaneously on an arbitrary rectangular family.

If their projected rows had positive nuisance-quotient rank on a desired
reservoir mismatch, `atlas-mixed-minor-needs-nuisance-quotient-rank` would
bound that mismatch by the two zero residuals in every amplification. The
free choice of `b_0,b_1` contradicts such a bound. Therefore this coupled
family contributes zero reservoir-authentication rank.
