---
rg: 2
id: full-mf-radical-locus-is-open-in-marked-groups
kind: claim
title: Full MF radical is an open condition on the space of marked groups
distinct_from:
  clopen-non-mf-cylinder: that exhibits one cylinder, cut out by the manuscript's forty-one literal relators and one inequation in eight generators, whose members are non-MF; this says every marked group with full MF radical has such a neighbourhood, in any number of generators, with the stronger conclusion.
  full-mf-radical-finite-challenge-cylinder: that cuts the cylinder with the given finite presentation of the saturated group; this cuts it with the relator list extracted from the linear inequality, so it applies to marked groups with no finite presentation.
  continuum-nonisomorphic-non-mf-cylinder: that asks how many isomorphism types one particular cylinder contains; this is a topological statement about the locus and asserts no multiplicity.
artifacts:
  - research/artifacts/mf-radical-linear-certificate-2026-09-07.md
  - non_mf_groups_exist.tex
---

In the space `G_m` of groups marked by `m` generators, the set

```text
{ (H,(h_i)) : Res_MF(H) = H }
```

is open.  A neighbourhood of a given point is cut out by the finitely many
relators `r_1,...,r_s` of `full-mf-radical-linear-relator-inequality`: the
set where each `r_j` is a relation is clopen, contains the given marked
group, and every member of it has full MF radical.  Adding one inequation
`v != 1` keeps the set clopen and makes every member nontrivial.
