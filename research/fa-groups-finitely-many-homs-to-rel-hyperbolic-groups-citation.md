---
rg: 2
id: fa-groups-finitely-many-homs-to-rel-hyperbolic-groups-citation
kind: route
title: Import Drutu--Sapir Corollary 4.37 with its standing assumptions, and Levitt Theorem 1.4
target: fa-groups-finitely-many-homs-to-rel-hyperbolic-groups
requires: []
---

## Drutu--Sapir

C. Drutu, M. Sapir, *Groups acting on tree-graded spaces and splittings of relatively hyperbolic
groups*, arXiv:math/0601305v2 (31 Jan 2006); Adv. Math. 217 (2008), no. 3, 1313--1367. Read from
the arXiv PDF on 2026-09-19 by swarm-0917-w17-w17-titz-break.

**Standing assumption of Section 4.3 (verbatim, p. 38 of the arXiv PDF).**

> From now on we fix an infinite finitely generated group G that is relatively hyperbolic with
> respect to a finite collection of finitely generated peripheral subgroups H = {H1,...,Hm},
> G ≠ Hi.

**Definition 4.18 (verbatim, p. 38).**

> Recall that Hi are called peripheral subgroups of G, subgroups of conjugates of Hi are called
> parabolic subgroups of G, conjugates of Hi are called maximal parabolic subgroups.

**Definition 4.31 (verbatim, p. 44).**

> A homomorphism φ : Λ → G is called parabolic if its image is a parabolic group.

**Corollary 4.37 (verbatim, p. 48).** It is Theorem 1.7 of the introduction.

> If a finitely generated group Λ satisfies property FA then for every relatively hyperbolic group
> G there are only finitely many pairwise non-conjugate non-parabolic homomorphisms Λ → G.

**Remark 1.13 (verbatim excerpt, p. 8).**

> A example is that of a finitely generated non-Abelian free group hyperbolic relative to a
> finitely generated non-Abelian free subgroup. [...] Still, for this example there exists a
> terminal point of the process, as the free group is hyperbolic relative to the trivial subgroup.

**The introduction's list of FA groups (verbatim, p. 6)** includes "all groups with Kazhdan
property T".

**How it is read.**
- A word-hyperbolic group is used as a relatively hyperbolic group with the single peripheral
  subgroup `{1}`. This is the convention of Remark 1.13. It is also the standard convention
  (hyperbolic relative to `{1}` is the same as hyperbolic), but that equivalence is not
  re-imported here.
- Under that convention the standing assumption requires `G` infinite and nontrivial, and a
  homomorphism is parabolic exactly when its image is trivial.
- For consumers who do not accept this convention, the hyperbolic case used downstream (a Kazhdan
  hyperbolic group has finite `Out`) is also given by Levitt below together with FA.

## Levitt

G. Levitt, *Automorphisms of hyperbolic groups and graphs of groups*, arXiv:math/0212088v1
(5 Dec 2002); Geom. Dedicata 114 (2005), 49--70. Read from the arXiv PDF on 2026-09-19.

**Theorem 1.4 (verbatim, p. 3).**

> Let G be a one-ended hyperbolic group. Then Out(G) is infinite if and only if G splits over a
> virtually cyclic subgroup with infinite center, as an arbitrary HNN extension or as an amalgam of
> groups with finite center.

The next sentence of the paper (verbatim):

> Paulin's theorem [11], together with Rips theory [2], provides a splitting over a virtually
> cyclic subgroup, but with no control on the center.
