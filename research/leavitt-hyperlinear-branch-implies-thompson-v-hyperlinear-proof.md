---
rg: 2
id: leavitt-hyperlinear-branch-implies-thompson-v-hyperlinear-proof
kind: route
title: Restrict the microstates to the embedded copy of V
target: leavitt-hyperlinear-branch-implies-thompson-v-hyperlinear
requires:
  - leavitt-cylinder-swaps-generate-thompson-in-el
artifacts:
  - notes/HYPERLINEAR_NONSOFIC_ATTEMPT_2026-08-26.md
---

By `leavitt-cylinder-swaps-generate-thompson-in-el`, Thompson's group `V`
embeds in `EL_D(R)` for the complete nine-leaf code `D`, hence in every group
containing `EL_D(R)`.  Hyperlinearity passes to subgroups: if
`u_n: G -> U(d_n)` are microstates of `G` (asymptotically multiplicative in
normalized Hilbert--Schmidt norm with `tr(u_n(g)) -> 0` for `g != 1`), their
restrictions to a subgroup are microstates of that subgroup.  Hence
hyperlinearity of `G` gives hyperlinearity of `V`.

For the Fournier--Facio group the same argument applies to the embedded
simple group `S` of `fournier-facio-torsion-free-skeleton`.
