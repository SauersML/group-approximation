---
rg: 2
id: binary-leavitt-two-shared-gauge-selector-compiler
kind: claim
title: Share one multiplicity involution across two incompatible binary selector rows
artifacts:
  - research/same-center-whitehead-analytic-candidate-package.md
  - research/same-center-whitehead-native-selector-subcorner-attachment.md
  - research/same-center-whitehead-native-occurrence-compiler-route.md
distinct_from:
  binary-leavitt-atomic-morita-return: that returns a Leavitt family to one prescribed sparse atom; this works on a positive-density packet carrier and needs only two scalar selector rows with a common external gauge.
  opnorm-leavitt-coarse-fine-return-row: that asks for one literal operator-norm coarse-to-fine support row; this permits both fine reflections to retain a nontrivial gauge and contradicts their two rank equations in normalized Hilbert--Schmidt norm.
  shared-gauge-cz-cancellation-needs-an-identity-outer-anchor: that asks for an identity-outer occurrence sharing the gauge and cancels it; this never cancels the gauge.
---

**OPEN FINITE-COORDINATE COMPILER.**  In the positive-density active-core
microstates of

```text
Delta=St_20(L_(F_2)(1,2)),       z=x_13(s_1t_1),
```

recover on one packet carrier two scale-changing selector rows with ratios

```text
(r_1,q_1)=(1/2,1/4),       (r_2,q_2)=(1/4,1/8),       (SGS1)
```

and prove, up to `o(1)` normalized-HS error, that their controlled
groupifications have the forms

```text
T_1=C_(1/4) tensor V_1,       T_2=C_(1/8) tensor V_2   (SGS2)
```

where `V_1,V_2` are unitarily conjugate inside the recovered multiplicity
reservoir, up to `o(1)` normalized-HS error.  Equivalently, it suffices to
prove that their positive spectral fractions differ by `o(1)`.  The carrier
mass must be bounded below by a constant depending only on the fixed
normal-generation data, not on the matrix dimension.

Once `(SGS1)--(SGS2)` are decoded, no further selector, projection, or
return theorem is needed.  By
`two-shared-gauge-selector-rows-have-an-affine-rank-obstruction`, the first
row forces the positive-sign fraction of `V_1` to converge to `1/2`, while
the second forces the positive-sign fraction of `V_2` to converge to `5/6`.
Their conjugacy makes those fractions asymptotically equal, and the robust
trace estimate gives a fixed HS defect floor on every positive-mass carrier.

This is a genuine weakening of the previous selector targets.  It does not
ask either `C_(1/4)` or `C_(1/8)` to be an ordinary group word, does not
select a sign eigenspace of `V`, and does not return a prescribed character
atom.  It asks only that the two scale-changing occurrences retain one
conjugacy class of external holonomy.  The recursive Clifford tail gives
literal equality in its
intended properly infinite representation and is finitely wordized by
`free-cone-shift-finitely-wordizes-recursive-clifford-tails`, but its current
relations admit finite stationary models in which parent and child gauges
are independent.  The missing theorem is therefore the native mixed-Leavitt
identification of those gauges, not recursive-tail syntax.

A sufficient analytic input is now only one fixed positive cross-Gram
condition.  After exactifying the two fixed packets,
`two-transport-cross-gram-has-a-fixed-mass-reducing-corner` extracts a
positive reducing polar corner; two mixed Pauli commutators then invoke
`two-mixed-pauli-commutators-lock-the-relative-reservoir-gauge`.  The old
common-bicommutant program additionally needed to eliminate every unused
tensor spectator and was invalidated there.  This compiler does not: the
affine rank parameter and its `1/3` defect floor are invariant under common
amplification and restriction to a reducing multiplicity subcorner.  Thus
the live native-Leavitt target is any fixed positive cross-Gram overlap for
two scale-changing coefficient transports, not mutual-commutant recovery.

Ordinary packet dressing cannot prove `(SGS2)` because it shares gauges only
inside one outer-automorphism class.  The two unequal-scale selectors must be
coupled by a Whitehead/Leavitt occurrence, a common coefficient Gram row, or
another matrix-only holonomy theorem.

The same-center Whitehead branch is now isolated at its exact boundary.
`same-center-whitehead-analytic-candidate-package` establishes the positive
carrier, common `M_8(C)` factor, conjugate Whitehead reservoir gauges, and the
two analytic unequal-label candidates.  The only remaining arrow on that
branch is
`same-center-whitehead-native-selector-subcorner-attachment`: authenticate
the actual native selector occurrences as those candidates on a positive
model-dependent subcorner.  The whole-carrier version is impossible, and the
full Gram of the two Whitehead unitaries does not imply the subcorner claim.

The scalar trace-cyclic triangle lemmas do not weaken this last requirement.
As recorded in
`trace-cyclic-balance-does-not-bypass-native-two-scale-occurrence`, their
third balance edge must already decode the two native gauge projections on
equal normalized carriers.  That is the same missing occurrence coupling in
scalar form, while the common-hidden-projection two-orientation lemma assumes
still more alignment.

The abstract theorem
`holonomy-rank-gap-is-a-carrier-local-mf-certificate` removes positive
ambient density from the **terminal** obstruction whenever the native words
are authenticated on one nonzero invariant carrier with operator-norm
control.  It does not remove the open native occurrence problem here:
neither the abstract rank polytope nor packet exactification proves that the
depth-one and depth-two Leavitt occurrences reuse one multiplicity state.
