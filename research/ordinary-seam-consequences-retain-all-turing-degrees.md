---
rg: 2
id: ordinary-seam-consequences-retain-all-turing-degrees
kind: claim
title: Ordinary normal consequence retains the entire seam word degree while MF consequence is one polynomial language
root: true
distinct_from:
  fixed-marked-mf-consequences-are-uniformly-polynomial: that computes MF semantics; this computes the ordinary consequence degree and exactly identifies when the two semantics disagree.
  sturmian-seam-normal-and-mf-consequence-is-polynomial-time: that treats fixed computable graph systems; this gives arbitrary ordinary consequence degrees with a fixed polynomial MF consequence operator.
artifacts:
  - research/artifacts/pestov91-fixed-mf-consequences-and-hidden-degrees-2026-09-13.md
---

For H_beta the full ordinary normal-closure consequence decision set has
Turing degree deg_T beta. Ordinary and MF consequences disagree exactly
when all premise words are identities and the output is a nonidentity
element of the MF radical L. Any premise set containing a genuinely
nontrivial relation makes the two consequence operators agree on all
outputs. Determining whether that relation is genuinely nontrivial need
not be computable. MF consequence itself is uniformly polynomial-time.
