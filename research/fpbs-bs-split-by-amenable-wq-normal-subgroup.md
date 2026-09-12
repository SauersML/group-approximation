---
rg: 2
id: fpbs-bs-split-by-amenable-wq-normal-subgroup
kind: route
title: Split nonamenable groups by whether they have an infinite amenable wq-normal subgroup
target: fpbs-benjamini-schramm-universal
requires:
  - fpbs-amenable-wq-normal-class-nonuniqueness
  - fpbs-no-amenable-wq-normal-class-nonuniqueness
---

Every nonamenable finitely generated group either has an infinite amenable
wq-normal subgroup or has none. The two premises cover the two cases for every
Cayley graph, so together they give the universal goal.

The split is not a restatement. In the first case
`fpbs-bs-iff-finite-relative-susceptibility` converts the gap into relative
subcriticality along the subgroup, using Hutchcroft--Pan's relative
Burton--Keane, relative sharpness and wq-normal uniqueness transfer. The second
case is where the group-level structure used by that reduction is absent.
