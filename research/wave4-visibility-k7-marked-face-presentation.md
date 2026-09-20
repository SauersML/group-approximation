---
rg: 2
id: wave4-visibility-k7-marked-face-presentation
kind: claim
title: The index-seven subgroup and its canonical central cover have an explicit six-face presentation and K7 has abelianization C7 to the fourth power
distinct_from:
  wave3-canonical-k7-class-has-primitive-evaluation: That pins the cohomology class and proves its evaluation ideal is Z; this gives a finite presentation marking that exact class and computes the complete integral abelianization of K7.
artifacts:
  - research/artifacts/hyperbolic-rf-wave4-class-two-2026-09-20.md
  - experiments/hrf-wave4-class-two-2026-09-20/vertex_weights.py
  - experiments/hrf-wave4-class-two-2026-09-20/vertex_weights.json
---

Put H0=K7 intersect <a,b>, H1=K7 intersect <b,c>, H2=K7 intersect <c,a>.
For i=1,...,6 define r_i as the product of the three separate vertex words

    (a^i b^-i)_H0 (b^i c^-i)_H1 (c^i a^-i)_H2.

Then K7=(H0*H1*H2)/<<r_1,...,r_6>>. The canonical face-zero cover is

    B_c0=<H0,H1,H2,z | z central, r_i=z^-1 for i=1,...,6>.

The central marking is the specified orbit face-zero cochain, with no
unspecified torsion-class addition. Reversing the common face orientation
inverts z. Moreover K7^ab=C7^4, as proved from the presentation and
independently checked by Reidemeister-Schreier exponent-sum rank.

DERIVATION
wave4-visibility-marked-face-presentation-proof
