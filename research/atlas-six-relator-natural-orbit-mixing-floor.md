---
rg: 2
id: atlas-six-relator-natural-orbit-mixing-floor
kind: claim
title: Every natural-orbit permutation escape from the six Atlas relators needs a mixed component of degree at least twelve
artifacts:
  - experiments/atlas_six_relator_blockwise_audit.py
  - experiments/atlas-six-relator-blockwise-audit.json
distinct_from:
  atlas-six-relator-has-no-a11-target: that exhausts pairs of nontrivial marked A8 maps in one natural degree-eleven ambient group; this identifies its unique five-row survivor and turns the degree-eleven census into a componentwise restriction in arbitrary degree.
  atlas-natural-a8-supports-collapse-before-collision: that uses all twelve cross-A4 packet edges to identify two natural supports in every alternating group; this uses only the five selected boundary relators and c_19243, but proves the weaker exact statement that a surviving permutation model must mix orbit blocks into components of degree at least twelve.
  atlas-six-relator-exact-phase-escape-is-a-finite-quotient-test: that characterizes arbitrary finite regular-margin escapes; this only excludes the block-diagonal and small-component permutation strata and leaves larger mixed components open.
---

Put

```text
Gamma_6=(A8_1*A8_2)/<<s_0,s_11,s_30,s_44,s_55,c_19243>>.
```

The unique natural `A11` chart satisfying the five boundary relators is the
aligned chart.  On that chart `c_19243` is a fixed-point-free involution on
the eight moving points, so it is not the identity.  This is not a numerical
coincidence: the five boundary rows select the classical alignment, while
the collision-centrality word reads the fixed nontrivial aligned involution.
In the `S3` relative normal form this is

```text
q_19243(I)=rho(b),
c_19243(I)=rho([p1_12,b]) != I.                       (PMX0)
```

The last permutation has order two and support all eight moving points.

There is also a componentwise all-degree consequence.  Let `Omega` be a
finite set and let

```text
alpha,beta:A8 -> Sym(Omega)                           (PMX1)
```

be permutation representations such that every nontrivial orbit of either
chart is the natural eight-point `A8` orbit.  If all six displayed relators
hold, then every orbit of

```text
<alpha(A8),beta(A8)>                                  (PMX2)
```

of size at most eleven is pointwise fixed by both charts.  Equivalently,
every nontrivial generated component has size at least twelve.

In particular the six relators have no exact permutation model obtained as
a blockwise direct sum of aligned or arbitrarily re-marked natural `A8`
blocks.  Any permutation escape must use genuine cross-orbit mixing: the
natural orbit partitions of the two charts must combine into a generated
component on at least twelve points.

## Proof

The exact replay first evaluates the three canonical strata of the literal
six frozen words.

* When the two charts are aligned, all five `s_j` are the identity, whereas
  `c_19243` has order two and support all eight moving points.
* If the first chart is trivial and the second is natural, `s_0` is a
  nonidentity involution (as are `s_30,s_55`).
* If the second chart is trivial and the first is natural, `s_11` is a
  nonidentity involution (as is `s_44`).

These are evaluations of fixed group words in `A8`, not character or
floating-point tests.  Precomposing a natural chart by any automorphism of
`A8`, including the outer automorphism, preserves nonidentity.  The
exhaustive `A11` census proves that exactly one labelled chart reaches
`c_19243`.  Since the aligned chart does so, it is that unique survivor; the
first bullet explains exactly why the last word rejects it.

Now let `Delta` be an orbit of the generated group in `(PMX2)` with
`|Delta|<=11`.  Restriction of either chart to `Delta` is a homomorphism from
the simple group `A8`; it is therefore trivial or injective.  Under the orbit
hypothesis, an injective restriction has exactly one natural eight-point
orbit and at most three fixed points.  Padding `Delta` by fixed points to
degree eleven gives one of the labelled cases in the exhaustive `A11`
census.

If both restrictions are nontrivial, the `A11` result says that the six
relators cannot all hold.  If exactly one is nontrivial, the corresponding
one-chart-trivial evaluation above already violates `s_0` or `s_11`.  Hence
both restrictions are trivial.  This proves the component statement.

## Exact remaining stratum

This theorem does not extend the `A11` exclusion to every sum of natural
orbits: the obstruction to doing so is now explicit rather than hidden.
When the two orbit partitions cross, their incidence graph can have
components of size at least twelve; on such a component one chart can carry
several coupled natural blocks, and the degree-eleven classification no
longer applies.  A finite permutation countermodel, if one exists, must live
in precisely this mixed stratum.  Direct-sum cancellation is impossible
because a group relator is the identity on a permutation direct sum exactly
when it is the identity on every component.
