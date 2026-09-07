---
rg: 2
id: fixed-gottschalk-test-group-is-surjunctive
kind: claim
title: The fixed all-group universal host is surjunctive
distinct_from:
  gottschalk-surjunctivity-fixed-two-generator-tester: that proves the tester equivalence; this asks for the still-missing positive assertion about its host.
  gottschalk-surjunctivity-conjecture: that quantifies over all groups; this isolates the single host used by the established reduction.
---

Fix the two-generator finitely presented all-group host U chosen in
universal-all-group-subgroup-colimit-class-tester and used in
gottschalk-surjunctivity-fixed-two-generator-tester. Every injective
finite-alphabet cellular automaton on A^U is surjective.

## Attempts

The existing marked-limit proof transports both a finite injectivity
detector and a finite missing-output cylinder. This proves permanence
and the tester reduction, but constructs no surjective preimage over U.
Finite presentation alone supplies neither finite models separating its
finite windows nor a proof that U is sofic. That shortcut is unsupported.

Applying the observable-defect theorem to an individual rule on U gives
an exact positive-rank tower if the rule is strict. No bound on those
windows is known here that forces its seed to vanish. A universal
sublinear-rank hypothesis is already false for a reversible rule over Z;
the quantitative criterion cannot simply be applied to every rule.
