---
rg: 2
id: single-block-conjugator-one-relator-groups-are-sofic
kind: claim
title: Every single-block Baumslag conjugator gives a sofic group
distinct_from:
  one-relator-groups-sofic: This covers the explicit family w=b^p a^s b^q in a nested Baumslag relation, not arbitrary one-relator presentations.
  one-sided-conjugator-one-relator-groups-are-sofic: That allows arbitrarily many indexed letters but requires one-sided support; this permits every ordering and collision of the three indices 0,p+q,q for one a-block.
  berlai-nonresidual-one-relator-families-sofic: That records the published pure-power and symmetric-conjugator families; this also covers asymmetric b^p a^s b^q and arbitrary integer a-block exponents.
artifacts:
  - research/artifacts/mixed-conjugator-one-relator-proof-2026-09-07.md
---

For all `p,q,s in Z` and `l,k in Z\{0}`, the group

    <a,b | (a^l)^(a^(b^p a^s b^q))=a^k>

is sofic, with `x^y=y^(-1)xy`.

The proof handles all distinct-index orderings and all degeneracies.
The case `p=-1,q=2,s=1,l=1,k=2` is the explicit mixed-conjugator question
in the introduction of Berlai's arXiv:2502.05064v1.

This is a written proof using established sofic permanence, not a
formalization in Lean. No literature-priority claim is made.
