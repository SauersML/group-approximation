---
rg: 2
id: cross-atlas-eleven-term-lift-construction
kind: route
title: Anchor the four generators, then solve the residual evaluation linearly and exhaust smaller corrections
target: leavitt-cross-atlas-eleven-term-s0-lift
requires:
  - binary-leavitt-unit-group-four-generated
artifacts:
  - experiments/kaplansky_affine_lift_search.py
  - experiments/kaplansky_minimum_lift_certificate.py
  - research/artifacts/kaplansky-cross-atlas-affine-lift-2026-09-07.md
---

## Proof

### Upper bound

Fix the four units of `binary-leavitt-unit-group-four-generated` as mandatory
terms of `A`.  Evaluation into the Leavitt algebra is `F_2`-linear on the
group algebra, so

```text
evaluation(A) = s_0
```

is one affine system over `F_2` once the mandatory part is moved to the right
side: the correction must evaluate to `residual = s_0 + evaluation(mandatory)`.
Coordinates come from the reduced binary-prefix normal form, expanded to a
common depth so that two elements are equal exactly when their expanded term
sets agree; a parity bit carried alongside the coordinates forces odd
correction weight, hence `eps(A) = 1`.  Over the radius-three Cayley ball in
the twelve adjacent transvections — `795` exact group elements — the system is
solvable with kernel dimension `703`, and sparse decoding returns the seven
words

```text
(1,0), (6,8), (0,2,9), (3,1,7), (5,3,1), (5,3,4), (5,11,10).
```

Adding the four mandatory terms gives `(ELA1)`; the eleven group elements are
pairwise distinct and the evaluation is checked term by term in the normal
form.  The support contains the four generators, so it generates `Q`.

### Lower bound in the anchored radius-three universe

Augmentation forces the correction weight to be odd, leaving `1, 3, 5` below
seven.  `experiments/kaplansky_minimum_lift_certificate.py` exhausts all three
weights exactly: weight one by direct comparison, weights three and five by
meet-in-the-middle over pair and triple sums keyed on the canonical normal
form.  None evaluates to the residual.  So seven is the minimum correction
weight and eleven the minimum total support, **after fixing those four
anchors and restricting corrections to the radius-three ball**.

Reproducers:

```text
python experiments/kaplansky_affine_lift_search.py \
  --lift-radius 3 --inverse-radius 3 --mandatory atlas4
python experiments/kaplansky_minimum_lift_certificate.py
```

The minimality is bounded twice over — by the anchor choice and by the ball —
and must not be quoted as a minimum support for lifts of `s_0` in general.
A different anchor set, or a correction outside radius three, may well do
better.
