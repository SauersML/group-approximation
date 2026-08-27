---
rg: 2
id: atlas-six-relator-has-no-a11-target
kind: claim
title: The Atlas six-relator quotient has no nontrivial two-chart homomorphism to A11
artifacts:
  - experiments/atlas_six_relator_a11_scan.py
  - experiments/atlas-six-relator-a11-scan.json
distinct_from:
  atlas-six-relator-quotient-identifies-h-bridge: that records the earlier natural A9 and A10 screens and the infinite surviving bridge; this exhausts the next alternating degree.
  atlas-a8-index-507-to-990-reaches-natural-a11: that classifies A11 as an ambient simple overgroup at index 990 for a larger Atlas packet; this directly evaluates the six relators on every labeled A8 pair in A11.
  atlas-six-relator-relative-small-cancellation-audit: that blocks a general residual-finiteness proof from metric small cancellation; this is a finite exact target exclusion.
---

Let

```text
Gamma_6=(A8_1*A8_2)/<<s_0,s_11,s_30,s_44,s_55,c_19243>>.
```

There is no homomorphism

```text
Phi:Gamma_6 -> A11                                      (A11S1)
```

whose restrictions to both marked `A8` factors are nontrivial.  Equivalently,
`A11` supplies no exact finite regular-margin countermodel to the Atlas
five-row phase lift.

More precisely, among all `6,652,800` labeled possibilities for the second
chart, the exact rejection counts at the first failed relator are

```text
s_0          6,650,496
s_11             2,292
s_30                 8
s_44                 2
s_55                 1
c_19243              1.                               (A11S2)
```

Thus exactly one labeled chart satisfies all five boundary relators, and it
fails `c_19243`.  No chart satisfies all six.

## Exhaustiveness

Every nontrivial homomorphism `A8 -> A11` is injective because `A8` is
simple.  Restrict the natural eleven-point action.  The subgroup-index list
of `A8` has no nontrivial index `9`, `10`, or `11`, and its unique degree-eight
permutation action up to automorphism is the natural action.  Hence the
restricted action has one eight-point orbit and three fixed points.

Fix the first labeled chart on points `1,...,8`.  Every second labeled chart
is therefore

```text
g alpha(-) g^-1,       g in S11,                       (A11S3)
```

where allowing odd `g` includes the outer automorphism of `A8`.  Right
multiplication by the pointwise centralizer `S3` of the source chart does not
change `(A11S3)`, and this is the entire redundancy.  The exact candidate
count is consequently

```text
|S11|/|S3|=11!/3!=6,652,800.                          (A11S4)
```

`experiments/atlas_six_relator_a11_scan.py` enumerates one representative
directly for every coset in `(A11S4)`, rather than constructing all `11!`
permutations.  It reads the six literal cyclically reduced words frozen by
`atlas-six-relator-relative-small-cancellation-audit`, maps every `4x4`
binary matrix through the certified exceptional isomorphism
`GL_4(2)~=A8`, and evaluates permutations exactly.  The assertion that all
`6,652,800` representatives were visited and the histogram sum are checked
in the script.  No floating-point calculation enters `(A11S2)`.

## Remaining exact gap

Together with the established A9 and A10 screens, this removes every
alternating target through degree eleven.  It does not exclude:

* alternating targets of degree at least twelve;
* other finite simple or almost-simple overgroups of `A8`;
* an unbounded sequence of finite images giving a matrix-ultraproduct escape.

There is no longer an independent finite-extension or solvable-radical
case: `atlas-six-relator-finite-escape-is-simple-test` sends every nontrivial
finite quotient to a larger nonabelian simple marked-`A8` quotient retaining
the bridge.  The unscreened exact target is therefore the finite-simple
overgroup family, while the uniform approximate gap remains separate.

Any one bridge-retaining finite target in those unscreened classes would
still refute `atlas-five-row-operator-phase-lift` by the regular
representation construction.
