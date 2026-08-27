---
rg: 2
id: atlas-l44-a8-brauer-normalizer-classification-proof
kind: route
title: Classify four-dimensional A8 modules in characteristic two and compute the subfield normalizer
target: atlas-l44-has-one-a8-class-with-self-normalizer
requires:
  - atlas-a8-index-44551-to-48960-reaches-l44
artifacts:
  - experiments/atlas_l44_a8_classification.py
  - experiments/atlas-l44-a8-classification.json
---

Use the characteristic-two Brauer table to show that the only nontrivial
composition factors of dimension at most four are the two dual degree-four
modules.  A faithful four-dimensional module is therefore irreducible and
is natural or contragredient.  Both have the same subgroup image
`GL4(2)<GL4(4)`, so there is one `L4(4)` class.  In the exact projective
85-point action compute centralizer order `1` and normalizer order `20160`.
Since `Aut(A8)` has order `40320`, the outer marking is unabsorbed.

