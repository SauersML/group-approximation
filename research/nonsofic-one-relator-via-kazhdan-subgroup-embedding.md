---
rg: 2
id: nonsofic-one-relator-via-kazhdan-subgroup-embedding
kind: route
title: Refute Pestov 4.10 by embedding a known nonsofic group in a one-relator group
target: nonsofic-one-relator-group
requires: []
artifacts:
  - research/artifacts/one-relator-soficity-audit-2026-08-17.md
---

Soficity passes to subgroups, so a nonsofic subgroup makes the ambient group
nonsofic.  Since August 2026 the shelf is stocked — Kun--Thom's wreath products
([[kun-thom-nonsofic-wreath]]) and Fournier-Facio's finitely presented
torsion-free example ([[fournier-facio-torsion-free-skeleton]]) — so the plan is
simply: embed one of them into a one-relator group and read off the answer.

**Dead: no such embedding exists, for any currently known nonsofic group.**  By
[[torsion-free-one-relator-has-no-kazhdan-subgroup]], a torsion-free one-relator
group is locally indicable and therefore contains no nontrivial finitely
generated Kazhdan subgroup; every known nonsofic group either has property (T)
or is built around an infinite finitely generated subgroup that does.  And the
torsion side is no escape: a one-relator group with torsion is virtually compact
special (Wise), hence residually finite, hence sofic, hence contains no nonsofic
subgroup whatsoever.

Both halves of the dichotomy close, which is why this is a structural kill and
not a report that the search was hard.

## What survives the demolition

The kill is keyed to **property (T)**, not to nonsoficity.  It says the current
generation of witnesses is unusable here, and it says something sharper about
what a usable one would look like: a nonsofic group that is itself **locally
indicable**, or at least has a nontrivial f.g. subgroup structure compatible with
every such subgroup surjecting onto `Z`.  No such group is known.  That is
recorded as attempt 6 of [[nonsofic-one-relator-group]] and is the honest
content of this route's failure — the negative lane is not blocked by a missing
embedding lemma, it is blocked by the absence of a nonsoficity mechanism that
does not use rigidity.

The route also does **not** kill the weaker plan of containing "enough of" a
nonsofic group; but that plan has no formulation that yields nonsoficity, since
soficity is not detected by proper subgroups.
