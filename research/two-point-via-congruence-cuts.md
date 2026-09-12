---
rg: 2
id: two-point-via-congruence-cuts
kind: route
title: Convert a cut certificate into two-point labels on the exact congruence model
target: two-point-orbit-approximation
requires: [marked-pair-cut-problem, pair-constraint-graph-criterion]
---

# Convert a cut certificate into two-point labels on the exact congruence model

Immediate composition.  Given `F` and `ε`, `marked-pair-cut-problem`
supplies `M` and `S ⊆ Q_M` of density `> 1-ε` separating `(s,p)` from
`(s,q)` in the restricted pair-constraint graph for every `s ∈ S`.  Item 1
of `pair-constraint-graph-criterion` (the ⟸ direction) converts the
component structure into label data: `B` = the components, `j_s(x)` = the
component of `(s,x)`, satisfying distinctness and every equivariance
clause.  The model map `φ_M : G → Sym(Q_M)` is an exact unital
homomorphism, hence `(F,ε)`-multiplicative in normalized Hamming for every
window and precision.  All clauses of the two-point definition at the
marked pair `(Γ, hΓ)` are met.

The role of `congruence-transporter-girth` is evidentiary rather than
logical, which is why it is not in `requires`: it shows the necessary
girth condition of the criterion is satisfied by these models once
`M ≥ 2·C(F)^{1/ε+2}`, i.e. that the cut problem is not vacuously false at
the levels the cut claim would use.
