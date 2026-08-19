---
rg: 2
id: common-quotient-onto-normal-subgroup-proof
kind: route
title: Hull's Corollary 7.4 with the suitable subgroup drawn from the normal subgroup
target: common-quotient-onto-normal-subgroup
requires: []
artifacts:
  - notes/TORSION_FREE_NORMAL_GENERATION_HULL_QUOTIENT.md
---

## Why sufficient

Complete written argument in the artifact, §4 (Lemma A and Theorem B), with
every cited statement quoted verbatim from the sources in §6.

Two steps.

**Lemma A.**  An infinite normal subgroup `D` of a torsion-free `G in AH` is
suitable with respect to any `A` for which `Gamma(G, A)` is hyperbolic and the
action is acylindrical and non-elementary (such `A` exists by [Hul16, Theorem
3.12(4)]).  Normality gives `|D^g cap D| = |D| = infinity`, so `D` is
s-normal, so it acts non-elementarily by [Osi16, Lemma 7.1]; and the third
clause of Hull's Definition 1.4 is vacuous because a torsion-free group has no
nontrivial finite subgroup ([Hul16, Lemma 5.5] restates suitability as
`K_G(D) = {1}`).

**Theorem B.**  Hull's proof of [Hul16, Corollary 7.4] with `h_1, h_2` taken
from `D` by [Hul16, Corollary 5.7] applied to `D` (which Lemma A now licenses)
rather than to `G_2`.  Corollary 5.7 supplies exactly the properties his
argument uses — infinite order, non-commensurable, `{<h_1>, <h_2>} ,->_h G_2`
— so Lemma 3.5, Lemma 5.8, and both applications of Theorem 7.1 run verbatim.
The first application gives `gamma(G_1) <= gamma(S_{suit}) <= gamma(D)`, the
second gives `Q = eta(gamma(G_1))`, and chaining the two inclusions gives
`alpha_2(D) = Q`.  Torsion (clause 3) is [Hul16, Theorem 7.1(e)] applied to
each of the finitely many small-cancellation steps; finite presentability
(clause 4) holds because the finitely generated case of Corollary 7.4 uses
only two applications of Theorem 7.1, each adding one relator per prescribed
element, and never the direct limit of Corollary 7.3.
