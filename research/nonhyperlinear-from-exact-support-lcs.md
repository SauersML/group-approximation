---
rg: 2
id: nonhyperlinear-from-exact-support-lcs
kind: route
title: An exact robust LCS sub-menu yields an explicit nonhyperlinear solution group
target: non-hyperlinear-group
requires:
  - mipstar-bcs-tracial-nonru-exists
  - exact-support-relator-sparsification
  - bcs-to-lcs-exact-support-gap
  - explicit-exact-support-lcs-witness
artifacts:
  - research/artifacts/lcs-exact-support-sparsification-2026-08-18.md
---

`mipstar-bcs-tracial-nonru-exists` supplies the unconditional noncommutative
source gap from `MIP*=RE`. The open compiler theorem
`bcs-to-lcs-exact-support-gap` asks for an LCS sub-menu which one tracial
assignment satisfies exactly and on which every finite-dimensional assignment
keeping the central mark separated has a positive defect somewhere.

The established `exact-support-gap-nonexact-checks-no-advantage` shows that this
is not genuinely weaker than perfect completeness of the **selected** LCS
sub-menu: if an ambient distribution has `g>q`, its exact support already has a
uniform constant gap. Ambient inexact checks are irrelevant to existence.

Once that exact robust sub-menu is available,
`exact-support-relator-sparsification` supplies the finite-moment extraction,
and `explicit-exact-support-lcs-witness` freezes one actual linear system and
its constants. The resulting solution-group mark `J` is nontrivial in an exact
tracial representation but trivial in approximate representations, giving the
nonhyperlinear endpoint.

The useful narrowing is therefore precise: the new mathematics is an
**exact-support sound compiler** from the tracial/non-`R^U` source to LCS, or an
equivalent direct exact robust LCS construction. Reweighting deliberately
inexact checks cannot replace that step.
