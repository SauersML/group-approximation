---
rg: 2
id: twisted-brin-thompson-groups-have-property-fa-citation
kind: route
title: Import property NL and FW_infty from Fournier-Facio--Wu--Zaremsky and turn NL into FA with Serre's lemma
target: twisted-brin-thompson-groups-have-property-fa
requires: []
artifacts:
  - research/artifacts/twisted-brin-thompson-fa-citation-check-2026-09-17.md
---

Citation import, checked by a written derivation. Source: F. Fournier-Facio,
X. Wu, M. C. B. Zaremsky, *Abstract twisted Brin--Thompson groups*,
arXiv:2603.24687v2 (revised 2 April 2026). The PDF was downloaded from arXiv on
2026-09-17 and its text extracted. Quotations below restore the spaces lost in
extraction and are otherwise verbatim.

**Q1 (Theorem 6.4).** "Let G be a group acting on a non-empty set S. Then SV_G
has property NL."

**Q2 (Definition 6.3).** "A group has Property NL, short for No Loxodromics, if
every action on a hyperbolic space is either elliptic or parabolic."
The paper also states (§1.4) that such groups "cannot act on a hyperbolic
space with a loxodromic element."

**Q3 (Corollary 6.6).** "Let G be a group acting on a non-empty set S. Then
SV_G has property FW_∞." With (§6.3) "We say that a group has property FW_∞ if
every action on a finite-dimensional CAT(0) cube complex has a global fixed
point."

**Q4 (faithful case, §2).** "if G↷S is faithful, then SV_G is a twisted
Brin–Thompson group, which here we may call a faithful twisted Brin–Thompson
group. This is a genuine group of homeomorphisms of C^S". The paper then
refers to "the definition in the faithful case from [BZ22]", that is
Belk--Zaremsky, arXiv:2001.04579.

In the faithful case the proof of Theorem 6.4 reduces to the earlier
[BFFG25, Proposition 5.23] (Balasubramanya--Fournier-Facio--Genevois,
*Groups Geom. Dyn.* 19(4), 2025), quoted in the paper as "SV_G has property NL
when G↷S is faithful [BFFG25, Proposition 5.23]". BFFG25 was not re-read.

**Finite generation.** Belk--Zaremsky, arXiv:2001.04579v2, Theorem A,
verbatim: "The group SV_G is finitely generated if and only if G is finitely
generated and the action of G on S has finitely many orbits."

## Derivation of FA

Let `H = SV_G` be finitely generated and act on a tree `T`. After barycentric
subdivision we may assume the action is without inversions, and a fixed vertex
of the subdivision is a fixed vertex or a fixed edge-midpoint of `T`.

Serre, *Trees*, §I.6.5: an automorphism of a tree without inversions is
elliptic or hyperbolic, and a finitely generated group acting without
inversions in which every element is elliptic has a global fixed vertex.

Suppose `H` fixes no vertex. Then some `h in H` is hyperbolic, with axis `L`
and translation length `l >= 1`. The geometric realization of `T`, with the
path metric, is a geodesic 0-hyperbolic space on which `H` acts by isometries.
For `x in L`, `d(h^n x, x) = |n| l`, so `n -> h^n x` is a quasi-isometric
embedding of `Z`, and `h` is loxodromic. This contradicts Q1 and Q2. So `H`
fixes a vertex. `∎`

Independently, `T` is a one-dimensional CAT(0) cube complex and a
simplicial action is cubical, so Q3 gives a fixed point of the realization. A
fixed point in the interior of an edge fixes that edge setwise, and without
inversions both endpoints are fixed.

## Trust surface

- Theorem 6.4 and Corollary 6.6 are consumed as stated. Their proofs rest on
  uniform perfectness (Theorem 6.2), relative simplicity (Theorem 3.6), BFFG25
  Proposition 5.23 and Genevois's criterion [Gen19, Theorem 5.1].
- Serre's lemma is standard and is already consumed in
  `research/artifacts/fg-perfect-wreath-c2-fa-proof-2026-09-17.md`.
