---
rg: 2
id: ccr-holds-for-all-genuine-fd-coordinate-models
kind: claim
title: Compressor-commutant rigidity holds for every genuine finite-dimensional coordinate model, with no collapse hypothesis
distinct_from:
  ccr-for-coordinate-collapsing-models: that proves the same ultraproduct conclusion under the extra hypothesis of image collapse, and spends its Step 3 converting Gamma-conjugation into Lambda-conjugation; this removes the hypothesis entirely by a dimension count on the exact coordinate commutants, and so also covers genuine coordinate chains that separate the two images.
  kt-centralizer-normalization-hs: that is the (CCR)/normalization question for ARBITRARY representations into the ultraproduct, which is the open problem; this settles only the genuine-coordinate regime, and its proof cannot reach approximate coordinates.
  compressor-coset-two-point-exact: that is the permutation-side residual visibility of compressor cosets in congruence quotients, a statement about cosets; this is a commutant equality that needs no congruence structure at all.
artifacts:
  - research/artifacts/fd-compressor-commutant-and-cycle-rounding-2026-09-12.md
---

**ESTABLISHED.**

**Theorem A.** Let `Gamma` be a group, `t` an element of an ambient group `G`
containing `Gamma`, and `Lambda = t Gamma t^-1` contained in `Gamma`. Then for
EVERY unitary representation `pi : G -> U(D)` on a finite-dimensional space,

```text
pi(Lambda)' = pi(Gamma)',
```

and `Ad pi(t)` restricts to a `*`-automorphism of `pi(Gamma)'`. No property (T),
no image collapse, no congruence structure, no hypothesis on `pi`.

**Corollary A1.** Let `Lambda <= Gamma <= G` with `Lambda` finitely generated
with property (T), and let `sigma = prod_U pi_n : G -> U(M)`,
`M = prod_U (M_(d_n), tr)`, be a coordinatewise ultraproduct of GENUINE
finite-dimensional unitary representations of `G`. Then

```text
sigma(Lambda)' ∩ M = sigma(Gamma)' ∩ M.
```

## Why it matters

- It removes the image-collapse hypothesis from
  `ccr-for-coordinate-collapsing-models`, whose proof consumed
  `compressor-coset-two-point-exact` for exactly that step. The coordinate input
  is free and structural.
- It closes the regime `kt-centralizer-normalization-hs` recorded as uncharted in
  its 2026-08-18 honesty amendment: genuine coordinate chains that SEPARATE
  `Lambda` from `Gamma` satisfy (CCR) as well, because separation of the images
  is irrelevant to their commutants.
- Consequently every counterexample to (CCR) is invisible coordinatewise. It must
  live entirely in the excess commutant, the Alekseev--Thom Open Problem 6.2
  locus, and NO exact finite-dimensional model can exhibit one however large its
  dimension. A finite-model hunt for a counterexample to (CCR) itself is futile;
  the remaining target is the approximate-coordinate regime alone.

## Scope

The proof is a dimension count, and dimension is exactly what the ultraproduct
lacks: there `dim` is replaced by a trace, and `A` properly contained in `u A u*`
with `A` isomorphic to `u A u*` is possible, as `R` inside `R` shows. Theorem A
therefore says nothing about approximate coordinates, which is where the open
problem lives. It also does not make individual almost-invariant projections of
the commutant close to invariant ones; see
`compressor-cycles-block-central-projection-rounding`, which refutes that in the
same models.
