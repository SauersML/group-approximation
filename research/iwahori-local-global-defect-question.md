---
rg: 2
id: iwahori-local-global-defect-question
kind: claim
title: Local Iwahori defect controls global distance to a compatible representation
artifacts:
  - research/artifacts/two-paper-ingestion-2026-08-19.md
  - research/artifacts/sl2-hnn-iwahori-dynamical-fork-2026-08-21.md
  - notes/HIGHEST_YIELD_NONHYPERLINEAR_ATTACK.md
distinct_from:
  iwahori-outlier-repair: that is this repository's proposed sufficient condition -- a full-rank repair theorem in the one sector its own analysis leaves open; this is the published question in Dogon-Vigdorovich's own local-defect/global-defect form, which the repair theorem is an attack on.
  iwahori-fractional-transport-integralization: that is one intermediate step of the attack, converting a fractional transport plan into orthogonal blocks; this is the whole question the attack is aimed at.
  iwahori-nielsen-extension-transversality: that asks for transversality of the two opposite modular extension loci, one ingredient of the attack; this is the global modulus question the attack is aimed at.
  iwahori-nielsen-hs-bilipschitz: that is a dimension-free bi-Lipschitz estimate for one fixed Nielsen involution on the coordinates of Z*C_2 representations; this is the existence of a global modulus relating local Iwahori defect to distance to the compatible subvariety, over the whole representation variety of the free product of two copies of SL_2(Z).
---

**Dogon--Vigdorovich, arXiv:2506.20843v2, Question 1.2** (`problem!` in the
source), stated in their notation.

Let `Lambda = SL_2(Z) * SL_2(Z)` and let `X_FD(Lambda)` be the representation
variety of all finite dimensional unitary representations, with
`d_2(pi, pi') = max_(s in S) d_2(pi(s), pi'(s))` for a fixed finite generating
set.  Let `B_+`, `B_-` be the upper and lower Iwahori subgroups of `SL_2(Z)`
(pullbacks of the upper and lower triangular subgroups of `SL_2(F_2)`, each of
index three), and let `sigma : B_+ -> B_-` be the isomorphism implemented by
conjugation by `t = diag(sqrt 2, 1/sqrt 2)`, an element of the commensurator
but not the normalizer of `SL_2(Z)` in `SL_2(R)`.

Call `pi in X_FD(Lambda)` **compatible** if its two restrictions satisfy
`pi_+|_(B_+) = pi_-|_(B_-) o sigma`; compatible representations form a
subvariety identified with `X_FD(SL_2(Z[1/2]))`.  With
`S_+ = {[[1,0],[2,1]], [[1,1],[0,1]], -I}` a generating set of `B_+`, define

```text
def(pi) = max_(s in S_+) d_2(pi_+(s), pi_-(sigma(s))),
D(pi)   = inf { d_2(pi, pi~) : pi~ in X_FD(Lambda) compatible }.
```

One always has `def(pi) <= 2 D(pi)`.  The claim is the converse modulus:

> There is `f : R_+ -> R_+` with `lim_(x->0) f(x) = 0` such that
> `D(pi) <= f(def(pi))` for every `pi in X_FD(Lambda)`.

Equivalently, by the congruence subgroup property of `SL_2(Z[1/2])`:
representations of `SL_2(Z)` that almost factor through a congruence quotient
`SL_2(Z/n)` with `n` odd are close to ones that genuinely do.

By `dv-s-arithmetic-hs-stable-nonhyperlinear-extension` and their
Corollary 1.3, a positive answer yields a non-hyperlinear finite central
extension of `SL_2(Z[1/2])`.

## Transcription note

The source also asserts, in **commented-out** text, that this question is
equivalent to Hilbert--Schmidt stability of `SL_2(Z[1/p])` and that `SL_2(Z)`
is Hilbert--Schmidt stable.  Those sentences are not printed in v2 and are not
used here.  Only the printed implication (positive answer implies a
non-hyperlinear group, their Corollary 1.3) is consumed.

## Attempts

- **Full-rank outlier repair.**  This repository's line of attack, recorded at
  `iwahori-outlier-repair` and fed by `iwahori-outlier-localization` and
  `edge-pair-mixed-gap-collapse`.  Its residual obstruction is physical rank,
  not Hilbert-space dimension: an `o(d^2)` low-energy operator space can still
  contain an invertible matrix, the scalar line being the example.
- **Spectral sparsity alone.**  Refuted for that reason; see the same node.
- **Bounded branching.**  Index-three restriction/induction has uniformly
  bounded branching (`notes/TRUE_IWAHORI_INDEX_THREE_HAS_BOUNDED_BRANCHING.md`)
  and this does not stop the identity's mass spreading over growing many
  cross-pairs.  Recorded negative.
- **Refutation by character rigidity is unavailable.**  By
  `character-rigidity-equals-hyperfinite-hs-stability`, stability implies
  character rigidity, so a failure of character rigidity would refute the
  question -- but `SL_2(Z[1/2])` is already known to be character rigid
  (Peterson--Thom), so that route is closed in advance.  The cheap negative
  answer does not exist.
- **Not attempted here: the negative side.**  No construction in this
  repository produces a sequence with `def(pi_n) -> 0` and `D(pi_n)` bounded
  below.  A negative answer would kill this route without touching the goal.
- **Tree-action falsification test.**  If the coset action
  `PSL_2(Z[1/2])` on `PSL_2(Z[1/2])/PSL_2(Z)` is sofic, finite-lamp action
  permanence makes its coset wreath product sofic and hence Connes
  embeddable.  The base lamp is then an exact relative-commutant leak, so the
  present stability claim is false.  The converse is not valid: nonsoficity
  of this action does not prove stability or nonhyperlinearity.  The precise
  implication audit is in the 2026-08-21 artifact.
- **The finite-index-double theorem does not settle the tree action.**
  Gao--Kunnawalkam Elayavalli--Mj prove soficity for doubles whose two
  finite-index edge embeddings are identical (and more generally for their
  consistently embedded graph-of-groups family).  The present Iwahori edge
  twist is not of that form.  As
  `finite-index-double-theorem-misses-iwahori-twist` records, it sends the
  primitive parabolic `u` to `u^2` and therefore cannot extend to an
  automorphism of `PSL_2(Z)`, already by abelianization `C_6`.  Thus the
  closest published graph-of-groups theorem cannot be used to declare the
  Bruhat--Tits vertex action sofic.

## Attempts (added 2026-08-21, from the HNN route)

- **This node now carries two routes to the goal.**  Besides
  `iwahori-sector-closure` (Dogon--Vigdorovich's finite central extension),
  `non-hyperlinear-from-hnn-over-sl2-z` shows a positive answer makes
  `<SL_2(Z[1/2]), t | [t, SL_2(Z)] = 1>` nonhyperlinear
  (`hnn-over-codense-kazhdan-subgroup-not-hyperlinear`,
  `sl2-z-inverse-p-over-sl2-z-is-codense-tau-pair`).  A negative answer
  would be witnessed by hyperlinearity of that HNN extension
  (`sl2-half-stability-excludes-hnn-hyperlinearity`).
- **Microstate form.**  By the congruence subgroup property every
  finite-dimensional representation of `SL_2(Z[1/2])` is a congruence
  representation, and by Peterson--Thom (arXiv:1303.4007, Theorem 2.6)
  every character is a finite-quotient character or the regular one; the
  finite-quotient part is handled by Dogon--Vigdorovich's hyperfinite
  stability (their Theorem 1.6, Proposition 8.3).  What remains is exactly:
  *every sequence of microstates of the regular trace of `SL_2(Z[1/2])`
  (defect tending to zero, traces tending to `delta_e`) is asymptotically
  close to direct sums of congruence representations.*  For a residually
  finite group this is equivalent to flexible stability (tensor a
  far-from-exact asymptotic representation with congruence representations
  of vanishing character), so nothing is lost in this form.
- **Linearization.**  Near a compatible representation `rho` (a congruence
  representation), first-order deformations of the pair `(pi_+, pi_-)` are
  cocycles `(c_+, c_-)` in `H^1(SL_2(Z), Ad rho) (+) H^1(SL_2(Z), Ad rho)`,
  the local defect is the image under restriction-minus-`sigma^*`-restriction
  in `H^1(B, Ad rho)`, and Mayer--Vietoris for the amalgam together with
  `H^1(SL_2(Z[1/2]), Ad rho) = 0` (vanishing for finite-dimensional unitary
  coefficients, from property (T;FD)) says that map is injective.  The
  question at first order is whether its inverse on the image is bounded
  *uniformly in `rho` and in the dimension* with respect to the normalized
  Hilbert--Schmidt norms on cochains; the full question adds the nonlinear
  terms.  Numerically (`experiments/iwahori_linearized_gap.py`, artifact
  Section 14) the smallest nonzero singular value of the mismatch map for
  the permutation representations of `SL_2(F_p)` on `P^1` is `0.82, 0.74,
  0.71, 0.57, 0.47, 0.41, 0.35, 0.27, 0.27, 0.30, 0.27, 0.26, 0.25, 0.21, 0.28`
  for `p = 3, ..., 53`: a transient, then fluctuation in `[0.20, 0.30]`
  with no trend, consistent with a positive floor; a positive floor is what would follow from Deligne's bound `|a_2| <= 2 sqrt 2 < 3` through the identity
  `||res_1 f - res_2 g||^2 = 3||f||^2 + 3||g||^2 - 2 Re <f, T_2 g>`.  A
  proof of uniform infinitesimal rigidity along these lines would be the
  natural first theorem toward this question; it would not settle it.
- **What a counterexample must look like.**  Exotic microstates of
  `SL_2(Z[1/2])`: defect and traces tending to zero, bounded distance from
  all congruence representations.  They cannot be built by perturbing
  congruence representations in the compatible directions (rigidity above)
  nor by tensoring them with anything exact; by
  `sl2-half-stability-excludes-hnn-hyperlinearity` they would also have to
  admit, to refute through the HNN group, an almost-centralizer of
  `SL_2(Z)` that is not an almost-centralizer of `SL_2(Z[1/2])`.
- **Deep-rank sibling (2026-08-21).**  This question is DV's Question
  1.4 (arXiv:2506.20843v2); its higher-rank lattice analogue is
  `sl3z-regular-microstates-are-congruence-correctable`, which the
  Weyl-sector route consumes at any `n >= 3` WITHOUT the central
  extension that forces DV to `SL_2` (infinite `pi_1`): the rank-two
  Weyl evaluation of `odd-congruence-lambda-exact-sector-collapses`
  replaces the extension mechanism.  Progress on either instance
  transfers its techniques, not its statement, to the other.
