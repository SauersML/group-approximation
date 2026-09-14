---
rg: 2
id: operator-mf-groups-embed-in-simple-kazhdan-mf-groups
kind: claim
title: Every finitely generated operator-MF group embeds in an infinite simple Kazhdan operator-MF group
distinct_from:
  hyperlinear-groups-embed-in-simple-kazhdan-hyperlinear-groups: that asks for tracial models of the envelope; this asks for operator-norm models.
  lef-iff-subgroup-of-simple-kazhdan-limit-of-finite-simple: that proves the envelope theorem for LEF inputs, which are operator-MF; this asks for all operator-MF inputs.
---

**OPEN.** Every finitely generated operator-MF group is a subgroup of an infinite finitely generated simple Kazhdan
group that is operator-MF.

## Attempts

- **Cost of the statement.** It forces a non-LEF infinite simple Kazhdan operator-MF group containing the finitely
  presented amenable Abels–Prüfer quotient, which is operator-MF by `amenable-implies-operator-mf`
  (`simple-kazhdan-envelope-theorems-force-non-lef-hosts`).
- **LEF hosts: dead for non-LEF inputs**, as in `hyperlinear-groups-embed-in-simple-kazhdan-hyperlinear-groups`.
- **Constraint on any host.** By the one-sided Kazhdan transport criterion of `non_mf_groups_exist.tex`, an operator-MF
  host `H` contains no configuration of a Kazhdan subgroup `L` and an element `u` with `uLu^(-1) ≤ L` together with a
  nontrivial normal Kazhdan subgroup of `H` inside the commutator defect of `L`. Every such configuration forces the
  identity map of `H`, a homomorphism to an MF group, to kill that normal subgroup.
