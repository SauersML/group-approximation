---
rg: 2
id: free-wreath-over-amenable-action-is-sofic
kind: claim
title: A free generalized wreath product over an amenable action is sofic, which would close the sofic compiler's positive branch
distinct_from:
  centralizing-hnn-perturbed-edge-separation: that is the Mikhailova-specific probabilistic Britton-separation lemma stated for the rope; this is the clean general statement it instantiates, over any amenable action, whose direct-sum analogue is a theorem.
  compiler-rope-is-coset-wreath-of-an-a-t-menable-base: that reframes the branch and records the absence of an obstruction; this is the precise sufficient lemma that would resolve it.
  amenable-base-makes-mikhailova-edge-co-amenable: that supplies the amenable action (co-amenable edge) the hypothesis of this claim needs; this is the wreath-soficity statement consuming it.
---

OPEN, and if established it proves
[[sofic-recognition-finite-presentations-is-pi2-complete]].

**Target.**  Let `H` be a sofic group, `G` a sofic group, and `alpha : H ↷ X`
an **amenable** action on a set (`ell^infinity(X)` carries an `H`-invariant
mean).  Then the free generalized wreath product

```text
G wr^*_(alpha) H = ( *_(x in X) G_x ) x| H
```

is sofic.

**Why it closes the branch.**  By [[centralizer-hnn-is-free-generalized-wreath]]
the compiler's inner rope is `Z wr^*_(H curvearrowright H/M) H` with
`H = F x F`.  Choosing an amenable Mikhailova base
([[mikhailova-coset-action-is-two-sided-q-action]]) makes `H curvearrowright H/M`
amenable ([[amenable-base-makes-mikhailova-edge-co-amenable]]), so the target
with `G = Z` gives the rope sofic — the positive branch of
[[sofic-safe-finite-presentation-compiler]].

**The direct-sum analogue is a theorem.**  For direct-sum lamps
`(bigoplus_X G) x| H`, soficity holds whenever `alpha` is a sofic action
(Gao--Kunnawalkam Elayavalli--Patchell, *Soficity for group actions on sets and
applications*, Thm. A), and amenable actions are sofic.  The whole content of
this claim is upgrading direct-sum lamps to free-product lamps.

## Attempts

- **Three favourable ingredients (for the compiler instance).**  `H = F x F` is
  residually finite (exact finite models); the free lamp group `*_X Z` is a free
  group, residually finite (reduced lamp words never collapse in its finite
  quotients — the Britton non-collapse is free); and the action is amenable
  (Følner sets in `X`).  Direct-sum soficity is known; free lamps are RF; the
  only coupling is the semidirect action, which is amenable.  This is the most
  favourable possible configuration for a free-wreath soficity proof.
- **Where a proof must do work (the sofic Ueda normal form).**  A finite model
  built on lamps over a Følner set `S subset X` truncates the free lamps to a
  finite quotient of `*_S Z` and lets `H` permute `S` up to boundary.  Two
  things need a uniform estimate: (i) the boundary of `S` under the tested
  `H`-ball is negligible (Følner, available); (ii) a Britton-reduced word
  `k_0 v^{e_1} ... v^{e_m} k_m` moves a fixed fraction of the model, i.e. the
  free-lamp syllables stay unreduced through the `H`-conjugations.  Step (ii) is
  the sofic analogue of Ueda's reduced HNN normal form; for the Mikhailova edge
  it is [[centralizing-hnn-perturbed-edge-separation]].
- **Why quotient models alone fail.**  If `H`'s finite model is an exact
  quotient, closure points of the stabilizer collapse the corresponding pinches
  ([[centralizing-hnn-sofic-via-regular-edge-centralizer]]); the model must be
  perturbed off a quotient on a vanishing Hamming set while keeping the lamp
  index action free and Følner.  Amenability of `alpha` is exactly what makes
  that perturbation budget available.
- **Scope caution.**  Over a NON-amenable action the analogue is false in the
  finite-lamp/direct-sum case (Kun--Thom: `(Z/2) wr_(G/Gamma) G` is nonsofic for
  an infranormal non-normal (T) pair, [[kun-thom-nonsofic-wreath]]); amenability
  of `alpha` (or at least soficity) is essential, and is why the amenable-base
  design of [[amenable-base-makes-mikhailova-edge-co-amenable]] matters.
