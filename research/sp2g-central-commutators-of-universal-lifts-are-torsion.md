---
rg: 2
id: sp2g-central-commutators-of-universal-lifts-are-torsion
kind: claim
title: In the universal cover of Sp_2g(R) every central commutator is torsion, so commuting pairs have commuting lifts
distinct_from:
  vcd-two-groups-contain-no-kazhdan-commuting-pairs: that is about Kazhdan commuting pairs inside groups of virtual cohomological dimension two; this is the vanishing of the commutator pairing of centrally commuting pairs in one Lie group cover, with no subgroup property.
  deligne-multiplier-trivial-on-sl2xsl2-and-parabolics: that uses commuting lifts only for preimages of commuting connected subgroups (a continuity argument) and restricts the multiplier to the product and parabolic subgroups; this kills the commutator pairing on every commuting pair of the whole real group, and hence on every abelian subgroup of every Deligne cover at once.
---

**ESTABLISHED.** Let `g >= 1`, `G = Sp_(2g)(R)`, let `p : G^ -> G` be the
universal cover, and put `Z^ = Z(G^)`, a finitely generated abelian group
containing `pi_1(G) = ker p = <zeta> = Z` with index 2 (it is `p^-1({+-1})`).

```text
a, b in G^,  [a,b] in Z^   ==>   [a,b] in Tors(Z^),   |Tors(Z^)| <= 2.    (CT1)
```

In particular, if `p(a)` and `p(b)` commute in `G`, then `[a,b] = 1`
(because `[a,b] in pi_1(G) cap Tors(Z^) = 1`), and the same holds in every
quotient `G^/C` with `C <= pi_1(G)`: commuting pairs of `G^/C` whose images
commute in `G` commute. In any quotient `G^/C` with `C` central and
`C >= Tors(Z^)`, every pair of elements whose commutator is central commutes.

This is D3 of
`research/artifacts/deligne-bounded-rank-rung-anatomy-2026-09-17.md`, now
made a node, with its proof reduced to one verbatim import (the
Guichardet--Wigner quasimorphism, in the form of Ben Simon--Burger--Hartnick--
Iozzi--Wienhard) and the centrally-commuting upgrade (CT1) that the
compression-defect kill `deligne-cover-compression-defects-are-trivial`
needs.

Derivation: `sp2g-central-commutators-of-universal-lifts-are-torsion-proof`.
