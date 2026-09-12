---
rg: 2
id: nonhyperlinear-from-oracular-2csp-canonical-groupifier
kind: route
title: Apply reverse Kleene to the marked canonical groupification of the Culf--Mastel 2-CSP family
target: non-hyperlinear-group
requires:
  - culf-mastel-oracular-2csp-perfect-gap-family
  - oracular-2csp-mark-relative-canonical-groupifier
  - canonical-profile-kleene-higman
---

Apply the groupifier to the computable family `B_m`.  If `m` halts, the
perfect CE model from `(CMG2)` and clause 1 show that `p_m!=0`.  If `m` does
not halt and a canonical-profile microstate sequence retained positive
`p_m`-mass, clause 2 would decode a perfect CE model of `B_m`, contradicting
the constant soundness gap in `(CMG2)`.  Hence every such sequence kills
`p_m`.

These are exactly `(CPK1)--(CPK2)` of
`canonical-profile-kleene-higman`.  Reverse Kleene followed by effective
Higman embedding therefore produces a finitely presented nonhyperlinear
group.

The order of limits removes all runtime dependence: for each fixed decoded
finite subsystem, first send the microstate defect and canonical trace error
to zero.  No uniformity in the machine runtime or in the depth of the
groupifier is used.
