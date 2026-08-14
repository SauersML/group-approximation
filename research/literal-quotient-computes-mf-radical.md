---
rg: 2
id: literal-quotient-computes-mf-radical
kind: route
title: Compute the literal MF radical from the marked quotient
target: literal-mf-radical-exact
requires: [literal-central-mark-corona-invisible, literal-mark-quotient-mf]
artifacts: [non_mf_groups_exist.tex]
---

## Why sufficient

The proved claim `literal-central-mark-corona-invisible` puts `w` in every
norm-matrix-corona kernel, so the central subgroup `<w> = {1,w}` lies in
`Rad_MF(E)`.  If `E/<w>` is MF, compose
the quotient map with a faithful corona representation of the quotient.  Its
kernel is exactly `<w>`, while the MF radical lies in the kernel of every
corona representation.  The reverse containment follows, giving
`Rad_MF(E) = {1,w}`.
