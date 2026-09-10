---
rg: 2
id: fpbs-contact-dispersion-sign-obstruction-proof
kind: route
title: Include mergers between neighbors when computing the root dispersion drift
target: fpbs-contact-dispersion-sign-obstruction
requires:
  - fpbs-cluster-contact-merger-balance
artifacts:
  - research/artifacts/fpbs/docs/cluster-contact-mergers.md
---

Section 3 computes all single-edge changes at the singleton partition.
Opening a root edge combines boundary contacts; opening an edge between
two root neighbors decreases dispersion without growing the root cluster.
The clique-product example gives -29/5, while the tree gives 143.
The small-p branching domination justifies the expectation derivative.
