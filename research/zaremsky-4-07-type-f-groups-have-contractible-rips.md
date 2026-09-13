---
rg: 2
id: zaremsky-4-07-type-f-groups-have-contractible-rips
kind: claim
title: "Zaremsky Problem 4.7 resolved: does every group of type F have a contractible Rips complex?"
root: true
distinct_from:
  zaremsky-4-03-rips-complex-of-zn-contractible: that is the question for Z^n with its standard word metric, answered yes by Virk; this asks about every group of type F and allows any finite generating set
  hyperbolic-rips-complex-models-proper-actions: that is the Meintrup–Schick model for proper actions of a hyperbolic group; this is Zaremsky's question for all groups of type F
  zaremsky-4-06-f-infinity-finite-cd-contractible-rips: that is Problem 4.6 for groups of type F_infinity with finite cohomological dimension, which contain the groups of type F; this is Problem 4.7 for groups of type F only
  zaremsky-4-04-type-fn-groups-have-connected-rips-complex: that asks for (n-1)-connected Rips complexes of groups of type F_n; this asks for contractible Rips complexes of groups of type F
---

M. C. B. Zaremsky, *Some open problems* (version of July 12, 2026,
https://zaremsky.github.io/open_problems.pdf), Section 4, Problem 7,
verbatim: "(Added 7/24/25): Relatedly, does every group of type F have a
contractible Rips complex?"

This claim is the question. It is established only through an answer route:

- **Yes**: `zaremsky-4-07-by-yes` requires
  `every-type-f-group-has-a-contractible-rips-complex`.
- **No**: `zaremsky-4-07-by-no` requires
  `some-type-f-group-has-no-contractible-rips-complex`.

Never write a `requires: []` route into this claim.

**Reading.** For a finitely generated group `G` with finite generating set `S`, `d_S` is
the word metric and the Rips complex `VR_r(G, d_S)` has the finite subsets of diameter
`≤ r` as simplices. A group of type F has a finite `K(G,1)`; such groups are torsion-free.
The literal reading (W), used by both answer claims: `VR_r(G, d_S)` is contractible for
SOME finite generating set `S` and SOME scale `r`. By
`group-rips-complexes-are-cayley-graph-flag-complexes` (canonical; Zaremsky already records
the rescaling to scale 1 in arXiv:1812.10976v3, Remark 6.6) this says: some Cayley graph of
`G` has a contractible clique complex, equivalently `G` acts freely, cocompactly and
vertex-transitively on a contractible locally finite flag complex. The natural
strengthening (R): some `S` makes `(G, S)` of type R (Li–Sánchez Saldaña,
arXiv:2608.24279v1, Definition 1.1: contractible for every `r ≥ r_0`), which is how they
read Problem 4.6 (their p. 2). A yes for (R) gives a yes for (W); a no for (W) gives a no
for (R). Zaremsky (arXiv:1812.10976v3, p. 20): "we do not know whether every group of type
`F_*` admits a contractible proper Vietoris–Rips complex."

**Relations to the list.** A yes to 4.6 gives a yes here; a no here gives a no to 4.6. A yes
here gives the conclusion of Problem 4.4 for groups of type F under reading (W). Thompson's
group `F` has no contractible Rips complex (`thompson-f-has-no-contractible-rips-complex`),
but it is not of type F.

**Established positive classes under (W)** (the last three unreviewed):

- torsion-free hyperbolic, CAT(0), and asymptotically CAT(0) groups, from Zaremsky's orbit
  theorem: `torsion-free-asymptotically-cat0-groups-have-contractible-rips`;
- torsion-free groups acting properly and coboundedly on coarsely injective spaces:
  `coarsely-injective-groups-have-contractible-rips-complexes`;
- torsion-free finite-index subgroups of hierarchically hyperbolic groups, e.g. of mapping
  class groups: `torsion-free-hhg-subgroups-have-contractible-rips-complexes`;
- all Helly groups, torsion allowed, with explicit scales:
  `helly-groups-have-contractible-rips-complexes`.

**Reported or imported classes for fixed generating sets (R):** hyperbolic groups with any
generating set (Rips; Bridson–Haefliger III.Γ.3.23); `Z^n` standard
(`rips-complexes-of-integer-lattices-are-contractible`); triangle-free RAAGs standard
(`triangle-free-raags-are-rips-type-r`); closure under finite-edge-group splittings
(`rips-type-r-closed-under-finite-edge-group-splittings`) and under direct products with the
`l^∞` generating set (`contractible-rips-groups-closed-under-direct-products`); all RAAGs with
the commuting-products generating set (reported by Li–Sánchez Saldaña p. 3 from
Chalopin–Chepoi–Genevois–Hirai–Osajda); groups satisfying Zaremsky's Asymptotic Link Criterion
(arXiv:1812.10976v3, Theorem 6.5).

## Attempts

- 2026-09-13 (z4-07-type-f-rips): every method above works through a small-ball property
  of a model space (Rips' thin triangles, Euclidean-type pinched link criteria, Helly or
  coarse Helly ball intersections), turned into contractibility by discrete Morse theory or a
  nerve theorem. It stops where a group of type F acts on no such space. Test objects for
  both answers: groups of type F with distorted infinite cyclic subgroups, such as the integral
  Heisenberg group and `BS(1,2)`. Hierarchically hyperbolic groups have undistorted abelian
  subgroups (Haettel–Hoda–Petyt), so these are outside that class; that they are outside every
  class above is expected but not verified here.
