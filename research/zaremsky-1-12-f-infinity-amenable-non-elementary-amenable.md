---
rg: 2
id: zaremsky-1-12-f-infinity-amenable-non-elementary-amenable
kind: claim
title: "Zaremsky Problem 1.12 resolved: is there an amenable, non-elementary amenable group of type F_infinity?"
root: true
distinct_from:
  fp-infinite-simple-amenable-group: that asks for a finitely presented infinite simple amenable group (the subject of Zaremsky 1.10); this asks for an amenable group of type F_infinity outside the elementary amenable class, with no simplicity requirement and a stronger finiteness requirement.
---

M. C. B. Zaremsky, *Some open problems* (version of July 12, 2026,
https://zaremsky.github.io/open_problems.pdf), Section 1, Problem 12, verbatim:
"Find an amenable, non-elementary amenable group of type F∞."

This claim is the question. It is established only through an answer route:

- **Construction**: `zaremsky-1-12-by-construction` requires
  `there-is-f-infinity-amenable-non-elementary-amenable-group`.
- **Nonexistence**: `zaremsky-1-12-by-nonexistence` requires
  `every-f-infinity-amenable-group-is-elementary-amenable`.

Never write a `requires: []` route into this claim.

**Reading.** A group `G` answers the problem when:

1. `G` is amenable;
2. `G` is not in Chou's class `EG` of elementary amenable groups, the smallest
   class containing all finite and all abelian groups and closed under
   subgroups, quotients, extensions and directed unions;
3. `G` is of type `F_∞`: some `K(G,1)` has finitely many cells in each
   dimension.

A finitely presented group of type `FP_∞` over `Z` is of type `F_∞`, so a
finitely presented amenable non-EA group of type `FP_∞` is an answer. The
problem says "find", so the natural answer is a construction. A proof that no
such group exists would also resolve it.

**What is known (bounded check, 2026-09-13; exact theorem numbers are fixed in
the `-citation` routes, not here).**

- *Finitely presented examples exist.* Grigorchuk, "An example of a finitely
  presented amenable group not belonging to the class EG" (Sb. Math. 189,
  1998), embeds the first Grigorchuk group `G` into a finitely presented
  ascending HNN extension `G~` built from Lysenok's presentation of `G`. `G~`
  is amenable and not elementary amenable. No source seen by this lane decides
  whether `G~` is of type `FP_3`.
- *Elementary amenable groups of type `FP_∞` are rigid.* By
  Kropholler–Martínez-Pérez–Nucinkis they are virtually soluble of finite
  Hirsch length with cocompact models for proper actions. So the non-EA
  condition is the whole difficulty.
- *Kropholler's theorem constrains every answer.* Torsion-free groups in
  Kropholler's class `H𝔉` of type `FP_∞` have finite cohomological dimension.
  Januszkiewicz–Kropholler–Leary (arXiv:0908.3669v1, p. 1) cite this as the
  key finiteness theorem for `H𝔉`-groups of type `FP_∞`, from Kropholler, "On
  groups of type (FP)_∞" (J. Pure Appl. Algebra 90, 1993), and note that
  Thompson's group `F` fails it. For finitely generated groups `LH𝔉 = H𝔉`.
  The same Kropholler paper is recalled as also bounding the orders of finite
  subgroups of `LH𝔉`-groups of type `FP_∞`; this lane has not yet read that
  part from the source. See
  `there-is-f-infinity-amenable-non-elementary-amenable-group` for the
  consequences.
- *Thompson's group `F`.* `F` is of type `F_∞` (Brown–Geoghegan) and is not
  elementary amenable. So `thompson-f-is-amenable` would answer this problem
  positively, and a nonexistence proof would prove `thompson-f-is-not-amenable`.
- Zaremsky lists the problem as open on July 12, 2026. The web search by this
  lane (2026-09-13, arXiv and general web; no MathSciNet or zbMATH) found no
  answer.

## Attempts

- 2026-09-13 (lane z1-12-amen-nonea): answer claims opened on both sides. The
  candidates are the HNN extensions of self-similar groups with finite
  endomorphic presentations, starting with Grigorchuk's `G~`; the structural
  fence is Kropholler's `FP_∞` theorem. Details in the answer claims.
