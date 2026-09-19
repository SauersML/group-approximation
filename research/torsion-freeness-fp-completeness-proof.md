---
rg: 2
id: torsion-freeness-fp-completeness-proof
kind: route
title: The rope is torsion-free and the seed Z/2 has torsion
target: torsion-freeness-of-finite-presentations-is-pi2-complete
requires:
  - finite-presentation-rice-criterion-via-the-fixed-positive-rope
  - mf-compiler-positive-branch-is-torsion-free
  - torsion-freeness-recognition-is-pi2-complete
---

Torsion-freeness passes to subgroups and is isomorphism invariant; the
compiler's positive branch is torsion-free
([[mf-compiler-positive-branch-is-torsion-free]]); `Z/2` is finitely
presented and has torsion.  Apply
[[finite-presentation-rice-criterion-via-the-fixed-positive-rope]] for
`Pi^0_2`-hardness, and the finite-presentation case of the `Pi^0_2` normal
form in [[torsion-freeness-recognition-is-pi2-complete]] for membership.
