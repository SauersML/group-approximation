---
rg: 2
id: alternating-schur-multiplier-citation
kind: route
title: Import the Schur multipliers of the alternating groups
target: alternating-groups-have-nonzero-schur-multiplier
requires: []
---

**Source.** Wikipedia, *Covering groups of the alternating and symmetric
groups*, raw wikitext (`action=raw`), fetched on MSI on 2026-09-13. The
paragraph beginning "Covering groups correspond to the second group homology
group" reads:

> "Covering groups correspond to the second [[group homology]] group, {{not a typo|H<sub>2</sub>(''G'', '''Z''')}}, also known as the [[Schur multiplier]]. The Schur multipliers of the alternating groups A<sub>''n''</sub> (in the case where ''n'' is at least 4) are the cyclic groups of order 2, except in the case where ''n'' is either 6 or 7, in which case there is also a triple cover. In these cases, then, the Schur multiplier is the cyclic group of order 6, and the covering group is a 6-fold cover."

**Match.** This is the statement of the target. The classical primary source
(Schur) was not read here.

**Hand sanity check for the nonvanishing, not needed for the import.** For
`n >= 5` the even permutation matrices give `A_n <= SO(n)`. The permutation
`(12)(34)` acts by `-1` on the plane spanned by `u = (e_1 - e_2)/sqrt(2)` and
`v = (e_3 - e_4)/sqrt(2)` and trivially on its orthogonal complement. So it is
the product of the reflections in `u` and `v`, and its lifts to `Spin(n)` are
`±uv`. These satisfy `(uv)^2 = -u^2 v^2 = -1`, so they have order `4`. Hence the
preimage of `A_n` in `Spin(n)` is a nonsplit central extension by `Z/2`. Since
`A_n` is perfect, a nonsplit central extension by `Z/2` has perfect total group,
and the five-term exact sequence then gives a surjection `H_2(A_n; Z) -> Z/2`.
