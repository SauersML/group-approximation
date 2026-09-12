---
rg: 2
id: ccr-holds-for-all-genuine-fd-coordinate-models
kind: claim
title: Compressor-commutant rigidity holds for every genuine finite-dimensional coordinate model, with no collapse hypothesis
distinct_from:
  commutant-no-growth: that is the COORDINATE statement, established and formalized as commutant_no_growth, that an endomorphism commuting with pi(t Gamma t^-1) already commutes with pi(Gamma) in a genuine finite-dimensional representation; this is the ultraproduct consequence, which additionally needs property (T) of the compressed copy and a conditional-expectation argument, and whose content is the removal of the collapse hypothesis from the coordinatewise route.
  ccr-for-coordinate-collapsing-models: that proves the same ultraproduct conclusion under the extra hypothesis of image collapse, and spends its Step 3 and its uniformity-in-lambda bookkeeping converting Gamma-conjugation into Lambda-conjugation; this removes that hypothesis by quoting commutant-no-growth at each coordinate, and so also covers genuine coordinate chains that separate the two images.
  kt-centralizer-normalization-hs: that is the (CCR)/normalization question for ARBITRARY representations into the ultraproduct, which is the open problem; this settles only the genuine-coordinate regime and cannot reach approximate coordinates.
  compressor-coset-two-point-exact: that is the permutation-side residual visibility of compressor cosets in congruence quotients, a statement about cosets; this is an ultraproduct commutant equality that needs no congruence structure at all.
artifacts:
  - research/artifacts/fd-compressor-commutant-and-cycle-rounding-2026-09-12.md
---

**ESTABLISHED.**

**Theorem.** Let `Lambda = t Gamma t^-1` be contained in `Gamma <= G` with
`Lambda` finitely generated with property (T), and let
`sigma = prod_U pi_n : G -> U(M)`, `M = prod_U (M_(d_n), tr)`, be a
coordinatewise ultraproduct of GENUINE finite-dimensional unitary
representations of `G`. Then

```text
sigma(Lambda)' ∩ M = sigma(Gamma)' ∩ M.
```

No image collapse, no congruence structure, no hypothesis on the coordinates
beyond their being genuine representations of `G`.

## Credit: the coordinate ingredient is not new

The per-coordinate input is the established, and Lean-formalized, claim
`commutant-no-growth` (`Criterion/CommutantRigidity.commutant_no_growth`): in a
genuine finite-dimensional representation, an endomorphism commuting with
`pi(t Gamma t^-1)` already commutes with `pi(Gamma)`, i.e.
`pi(Lambda)' = pi(Gamma)'`. That statement is theirs, and this node claims none
of it.

The artifact records a second, one-line derivation of it by dimension count:
`pi(Lambda)' = pi(t) pi(Gamma)' pi(t)*` has the same finite dimension as
`pi(Gamma)'` and contains it, so the two are equal. That is an alternative proof
of a known result, offered only because it makes the scope obvious — no property
(T), no hypothesis on `pi` — and because it shows exactly which ingredient the
ultraproduct lacks, dimension being replaced by a trace.

## What is new here

The ultraproduct corollary, and specifically the removal of the hypothesis.

- `ccr-for-coordinate-collapsing-models` proves the same conclusion assuming
  image collapse `pi_n(Gamma)` contained in `pi_n(Lambda)`, and consumes
  `compressor-coset-two-point-exact` to get it. Quoting `commutant-no-growth`
  at each coordinate makes that step unnecessary: the two exact coordinate
  commutants are equal for structural reasons, collapse or no collapse.
- This closes the regime `kt-centralizer-normalization-hs` recorded as uncharted
  in its 2026-08-18 honesty amendment — *genuine coordinate chains that SEPARATE
  `Lambda` from `Gamma` (if any exist for `G`); the collapsing-regime proof says
  nothing there.* Separating genuine chains satisfy (CCR) too, because
  separation of the images is irrelevant to their commutants.
- Consequently every counterexample to (CCR) is invisible coordinatewise: it must
  live entirely in the excess commutant, the Alekseev--Thom Open Problem 6.2
  locus, and NO exact finite-dimensional model can exhibit one, however large its
  dimension. A finite-model hunt for a counterexample to (CCR) itself is futile,
  and the remaining target is the approximate-coordinate regime alone.

## Scope

Nothing here touches approximate coordinates, where the open problem lives: for
approximate coordinate maps there is no representation `pi_n` of `G`, so
`pi_n(Lambda)` is not a unitary conjugate of `pi_n(Gamma)` and
`commutant-no-growth` has nothing to apply to. Nor does it make individual
almost-invariant projections of the commutant close to invariant ones; see
`compressor-cycles-block-central-projection-rounding`, which refutes that in the
same models.
