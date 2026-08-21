---
rg: 2
id: authenticated-pauli-branch-needs-source-saturation
kind: claim
title: An authenticated Pauli branch is stationary until both children saturate the same source
distinct_from:
  mixed-pauli-commutator-authenticates-one-capacity-cut: that identifies the leakage energy with one authenticated root involution; this tests whether survival of that involution alone supplies a binary multiplicity recurrence.
  pauli-two-child-transfer-packet: that constructs one exact equal-trace branch in the atlas packet; this gives the abstract scalar recurrence, an exact stationary Pauli countermodel, and the universal-trace firewall for iterating the branch.
  approximate-relative-leavitt-cell-kills-active-trace: that uses decoded two-sided Leavitt inverse and range-sum relations to kill a projection; this isolates the weaker two scalar source-saturation moments needed for one branching step.
---

An authenticated Pauli involution and two orthogonal child carriers do not by
themselves yield a contractive multiplicity recurrence.  The extraspecial
two-pair packet has an exact stationary countermodel.  If both child maps
instead saturate the same source projection `P`, then for contractions `S_i`
with range leakage `lambda_i` into orthogonal `B_i`,

```text
tau(P) <= (tau(B_0)+tau(B_1)
           +alpha_0+alpha_1+lambda_0^2+lambda_1^2)/2,
alpha_i=||S_i^*S_i-P||_2.
```

Thus the missing datum is source saturation, not authentication of the Pauli
sign or orthogonality of the child ranges.
