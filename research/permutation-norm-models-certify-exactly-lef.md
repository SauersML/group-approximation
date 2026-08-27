---
rg: 2
id: permutation-norm-models-certify-exactly-lef
kind: claim
title: Permutation operator-norm models certify exactly the LEF groups, so the Folner route cannot reach amenable MF
distinct_from:
  lef-implies-operator-mf: that is the one useful direction, LEF implies MF, and says nothing about what the permutation construction fails to reach; this is the equivalence together with the rigidity dichotomy that makes the converse true, and its point is the *limit* of the construction.
  cyclic-base-sharpness: that claim is about the marked word of the literal cyclic-base analogue and its detection by an amenable Clifford quotient; this one is about the approximation-theoretic reason the amenable side of that argument cannot be certified elementarily, and it applies to every group, not just that quotient.
  commuting-lamp-quotient-mf: that asks whether one specific quotient is MF, and its exact-finite-model route is dead because the base has property (T); this is the general theorem saying why *no* permutation-model route reaches MF beyond LEF, for a reason that has nothing to do with (T).
  kazhdan-projection-not-in-l1: that says why the property-(T) averaging machinery is unavailable in the operator-norm corona, so that every (T) argument must first pass to the adjoint corona and terminate in the 2-norm; this says why the *Folner* machinery is unavailable there, for an unrelated reason -- permutation matrices are one apart -- and it involves no Kazhdan group, no averaging, and no projection.
artifacts:
  - non_mf_groups_exist.tex
  - GroupApproximation/Analysis/AmenableQuasidiagonal.lean
  - GroupApproximation/Algebra/AmenableMFProof.lean
  - GroupApproximation/Monsters/CyclicBaseLEFObstruction.lean
---

Call a group **permutation-norm-modelled** when every finite test set carries a
finite model assigning permutations to group elements, injectively on the test
set, with operator-norm multiplicativity defect strictly below `1` there.  That
is the shape of every model the Følner construction produces: permutation
unitaries, separation by injectivity, multiplicativity in operator norm as MF
demands.  Then:

- a permutation-norm-modelled group is **LEF**, and conversely every LEF group
  is permutation-norm-modelled with defect exactly `0`.  So the construction
  detects **exactly** the LEF groups and nothing beyond them;
- the reason is an absolute rigidity, not quantitative slack: two *distinct*
  permutation matrices are at `l^2`-operator distance at least `1`, so the
  operator-norm distance between permutation matrices, and the operator-norm
  multiplicativity defect of a permutation model, take **no value strictly
  between `0` and `1`**.  An operator-norm model built from permutations is
  approximate only if it is exact;
- consequently a *positive* normalized Hamming defect, however small, already
  forces operator-norm defect at least `1`; Følner averaging buys nothing in
  operator norm, and at every accuracy there are permutation pairs with Hamming
  distance below `eps` and operator distance at least `1`;
- applied to the manuscript's own object: the realized Clifford quotient is
  amenable and admits **no** permutation operator-norm model at any accuracy.

## What this settles about the manuscript's "amenable, hence MF"

`non_mf_groups_exist.tex` invokes *amenable implies MF* in three places — the
introduction's "and, by quasidiagonality, all amenable groups", the paragraph
*Sharpness of the Kazhdan hypothesis* ("is a subgroup of this amenable group
and is therefore amenable, hence MF by [TWW]"), and the saturated-defect
sentence about homomorphisms into amenable groups.  Every step of that sentence
is machine-checked except the last, and this claim is what the last one costs.

The word *quasidiagonality* in the introduction is not decoration: it marks the
exact point at which the implication stops being elementary.  The naive route —
Følner set, complete each translation to a permutation of it, use those
permutation matrices as the finite-dimensional almost representation — produces
*soficity*, because the Hamming defect of the completion is controlled by the
Følner boundary.  It cannot produce MF, and the obstruction is absolute.  The
dichotomy is recorded not only on the abstract shape but directly on the
repository's own Følner permutations (`folnerPerm_l2_opNorm_defect_eq_zero_or_one_le`).

**Tikuisis--White--Winter is not proved here and nothing stands in for it.**
Every positive MF result in the repository —
`isOperatorMF_of_residuallyFinite`, `isOperatorMF_of_isLEF`,
`isOperatorMF_of_locallyFinite` — factors through *exact* finite models, and
this claim says the Følner construction cannot escape that class.  Certifying
the manuscript's sentence requires genuinely non-permutation unitaries, which
is exactly the quasidiagonality input.  The reachable case is recorded
alongside: for locally finite groups both halves, amenability and MF, are
machine-checked, and the same holds for residually finite amenable groups.  No
amenable group outside the LEF class is certified MF anywhere in this
repository.
