---
rg: 2
id: free-wreath-over-amenable-action-is-sofic
kind: claim
title: A free generalized wreath product over an amenable action is sofic (false as stated, refuted)
refuted_by:
  - free-wreath-over-an-amenable-action-can-be-nonsofic
distinct_from:
  centralizing-hnn-perturbed-edge-separation: that is the Mikhailova-specific probabilistic Britton-separation lemma stated for the rope; this was a general statement over any amenable action, now refuted, and its direct-sum analogue is false as well.
  compiler-rope-is-coset-wreath-of-an-a-t-menable-base: that reframes the branch and records the absence of an obstruction; this was a proposed sufficient lemma, refuted, which would not have reached the compiler's non-amenable Higman-host edge in any case.
  amenable-base-makes-mikhailova-edge-co-amenable: that supplies a co-amenable edge; this was the wreath-soficity statement consuming it, refuted in general, although the amenable-base instance is sofic because its action factors through an amenable group.
---

**REFUTED (2026-09-13, lane `ex2-free-wreath-amenable-sofic`).**
[[free-wreath-over-an-amenable-action-can-be-nonsofic]] takes the sofic lamp
group `Z`, the sofic actor `H = G' wr Z` over a Kun--Thom pair `(G', Gamma)`,
and an amenable transitive action `H ↷ H/K`. The resulting free wreath product
contains the nonsofic Kun--Thom double `G' *_Gamma G'`. The false step is the
principle "amenable actions are sofic"
([[amenable-action-of-a-sofic-group-need-not-be-sofic]]).

**Original target (kept for the record).** Let `H` be a sofic group, `G` a
sofic group, and `alpha : H ↷ X` an amenable action on a set. Then
`G wr^*_(alpha) H = ( *_(x in X) G_x ) x| H` is sofic.

## Corrections to the original remarks

- **"Why it closes the branch."** This was wrong for two reasons. (i) The
  claim is false. (ii) Even the true amenable-image case does not reach the
  compiler. The compiler's Mikhailova base is the Higman host `H_e` of
  `Q_e = B3(S_c)` (item 4 of
  `research/artifacts/mf-fp-pi2-unconditional-assembly-2026-08-26.md`). `H_e`
  contains the free group `F(x,y)`, so it is non-amenable on every branch, and
  a base "chosen amenable by design" cannot carry the switch. The positive
  branch also needs the second, twisted rope over `S_e = F *_(N_e) F^v`, and
  that rope is not a free wreath product.
- **"The direct-sum analogue is a theorem ... amenable actions are sofic."**
  This is false in the same example: `(Z/2) wr_(H/K) H` is nonsofic. GKP
  Theorem 3.6 needs a *sofic* action.
- **"The whole content of this claim is upgrading direct-sum lamps to
  free-product lamps."** That upgrade is GKP Theorem 3.7, already in the graph
  as [[gkp-free-generalized-wreath-soficity]]. In every application the
  missing input is soficity of the action.

**What is true.** If the action factors through an amenable quotient of `H`,
the free wreath product is sofic (GKP Theorems 2.17 and 3.7, Proposition
2.15(1)). More generally, a transitive amenable action is sofic exactly when
its restriction to a point stabilizer is sofic (`co-amenable-induction-of-sofic-actions`),
and then GKP Theorem 3.7 applies.

## Attempts

(History, superseded by the refutation.)

- **Three favourable ingredients (for the compiler instance).** `H = F x F`
  is residually finite, the free lamp group `*_X Z` is residually finite, and
  the action was assumed amenable. The counterexample shows that these three
  properties are not jointly enough in general, because amenability of the
  action does not control the stabilizer's action on `X`. The
  residually finite a-T-menable case stays open
  ([[compiler-rope-is-coset-wreath-of-an-a-t-menable-base]]).
- **Where a proof must do work (the sofic Ueda normal form).** Models built on
  lamps over a Følner set `S subset X` handle boundary effects. The labelling
  condition of GKP Definition 2.1(3) is the real requirement, and it asks
  that the point stabilizer's action on `X` be modelled. For the Mikhailova
  edge see [[centralizing-hnn-perturbed-edge-separation]].
- **Why quotient models alone fail.** If `H`'s finite model is an exact
  quotient, closure points of the stabilizer collapse the corresponding
  pinches ([[centralizing-hnn-sofic-via-regular-edge-centralizer]]).
- **Scope caution.** Over a non-amenable action the direct-sum analogue is
  false (Kun--Thom, [[kun-thom-nonsofic-wreath]]). The refutation shows that it
  also fails over some amenable actions.
