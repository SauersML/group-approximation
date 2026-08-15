---
rg: 2
id: hyperlinear-trace-not-mf-trace
kind: claim
title: A hyperlinear trace that is not an MF trace
distinct_from:
  hyperlinear-not-imply-mf: That established claim is the group-level separation; this is its trace-level consequence for a single trace on a single C-star algebra, and it answers a question posed in the literature.
  mf-hyperlinear-radical-divergence: That claim separates two radicals elementwise inside one group; this one separates two classes of traces on a C-star algebra.
artifacts:
  - non_mf_groups_exist.tex
  - GroupApproximation/Endpoint/NonMFImpact.lean
---

There is a separable unital C-star algebra carrying a trace which is
hyperlinear but not MF, in the senses of Shulman, *Sections and cones*,
arXiv:2507.22783v3.  Take `A = C^*(W)` for the sofic non-MF witness `W`, with
`tau` its canonical trace.

This answers, negatively, one of the two converse implications that paper
records as open.  Verbatim from v3: "Clearly every quasidiagonal trace is
amenable and every MF-trace is hyperlinear.  Whether the converse
implications hold is an open problem."  The present claim refutes
`hyperlinear => MF`.  It says nothing about `amenable => quasidiagonal`,
which involves completely positive maps and remains open.

The contrast with that paper's Theorem 30 --- "all hyperlinear traces on
cones are MF" --- is exactly a contrast: a cone is homotopically trivial and
its traces are soft, whereas the obstruction here is the property-`(T)`
compression rigidity that makes `W` non-MF while `W` is sofic.

Consequence for this repository: the non-MF theorem has a trace-level
corollary in the operator-algebra literature's own vocabulary, independent of
the group formulation.
