---
rg: 2
id: line-groups-with-bounded-support-lack-bvc
kind: claim
title: "A group of homeomorphisms of the line without global fixed point containing a compactly supported element with finitely many support components does not have BVC"
---

Let `G <= Homeo^+(R)` have no global fixed point.  Suppose `G` contains
`g != 1` whose support `supp(g) = {x : g(x) != x}` lies in a bounded interval and
has finitely many connected components.  Then `G` does not have BVC.  The
same holds for `G <= Homeo^+([0,1])` acting on `(0,1)` without a global fixed
point there.

This needs no abelianization or torsion hypothesis, so it covers simple
groups.  Examples: Thompson's F and its commutator subgroup `[F, F]`, and
every group of piecewise linear or piecewise projective homeomorphisms of an
interval with a compactly supported element and no interior global fixed
point.  Von Puttkamer--Wu rule out F through `H_1(F) = Z^2`
(arXiv:1607.03790v2, Example 1.16), which does not reach `[F, F]` or simple
examples.

Proof: `line-groups-with-bounded-support-lack-bvc-proof`.
