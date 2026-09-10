---
rg: 2
id: fpbs-infinite-contact-zero-relative-cost
kind: claim
title: Connected infinite contacts give zero relative repair cost on the original action
distinct_from:
  fpbs-finite-index-star-relative-cost: that connects finitely many subrelation classes through a small complete section; this allows infinitely many classes and uses infinitely many edges between adjacent classes
artifacts:
  - research/artifacts/fpbs/docs/shared-component-repair.md
---

Let H be a simple finite-cost generating graphing of a free p.m.p.
action of a countably infinite group, and S a measurable subrelation
of its orbit relation R. In each orbit, connect two S-classes when
infinitely many H-edges run between them. If this graph of classes
is connected almost surely, then relC(R;S)=0. Repairs are measurable
on the original probability space. In particular C(R)<=c(F) for
any finite-cost graphing F of S satisfying the hypothesis.

The proof first samples sparse vertex marks and then transfers
finitely many connection tests to finite atom colorings on the
original free action, paying all failed tests and the entire tail
of H. No cost-invariance theorem for an auxiliary action is assumed.

Sections 3--4 audit a possible source of the hypothesis. Relative
determinantal cycle deletion leaves a component quotient with no
nonempty finite cut. A recursive parallel-path graph shows that
this weaker property alone does not guarantee connection by a
positive-density independent sprinkling. No assertion about a
universal rounding rule or a resolution of Fixed Price is made.
