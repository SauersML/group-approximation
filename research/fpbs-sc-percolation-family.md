---
rg: 2
id: fpbs-sc-percolation-family
kind: claim
title: All locally finite Cayley graphs in the explicit family have p_c<p_u
root: true
---

**Statement.** Theorem 1(6) of the small-cancellation note: for every locally finite Cayley graph C
of every group G(p,I) in the family, Bernoulli bond percolation satisfies p_c(C) < p_u(C), and every
parameter strictly between the two thresholds has infinitely many infinite clusters almost surely.
The interval is not numerically bounded by this route.

**Proof location.** `research/artifacts/fpbs/small-cancellation-family.md`, Section 7; response 38.
The deduction is two lines: the groups contain <a^2,b^2> isomorphic to F_2 and so are not virtually
cyclic, which turns the Gruber-Sisto dichotomy into acylindrical hyperbolicity, and Choi-Seo then
gives the nonuniqueness phase on every Cayley graph.

**Imported inputs.** Gruber-Sisto, *Infinitely presented graphical small cancellation groups are
acylindrically hyperbolic*, arXiv:1408.4488v3, Theorem 1.3, whose classical C(7) case covers C'(1/6)
with proper-power relators. Choi-Seo, *Percolation in acylindrically hyperbolic groups*,
arXiv:2508.08932v2. Both identifiers resolve with matching titles and authors.

**Finite-replay evidence.** None, and none is possible: the two substantive steps are imported
theorems about infinite groups. The archive's own contribution here is the verification that the
family is not virtually cyclic, which the free subgroup of Section 3.2 supplies.

**Evidence level.** Import plus a one-step deduction. The only new mathematics is the exclusion of
virtual cyclicity. This settles Benjamini-Schramm for one explicitly presented family and says nothing
about arbitrary nonamenable Cayley graphs.

Status records a written deduction or imported theorem, not independent mathematical verification.
