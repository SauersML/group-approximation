---
rg: 2
id: kawauchi-dependency-audit
kind: route
title: Read the claimed proof's own abstracts and record what they invoke
target: kawauchi-weak-kervaire-rests-on-unresolved-inputs
requires: []
artifacts:
  - research/artifacts/kervaire-laudenbach-audit-2026-08-17.md
---

Citation audit, performed 2026-08-17 by reading the arXiv abstract pages of
arXiv:2303.13728 and arXiv:2212.02617.  Both quotations in the target claim
are verbatim from those pages; the dependency on the smooth unknotting
conjecture and the smooth 4D Poincaré conjecture is declared in the
supporting manuscript's own abstract, so establishing the target requires no
judgement about the interior of either proof.

What was **not** done: the bodies of the two manuscripts were not read, the
third manuscript in the chain (arXiv:2303.04368) was not fetched, and no
attempt was made to evaluate the claimed four-dimensional results
themselves.  None of that is needed for the statement as scoped — the claim
is about what the chain invokes, not about whether it succeeds.

House rule this follows: a claimed resolution of a major open problem enters
this graph as an *established input* only after its own dependencies are
found closed.  Here they are declared open by the authors' own abstract, so
the import route is dead and the conjecture stays open.
