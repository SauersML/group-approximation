---
rg: 2
id: simple-kazhdan-lef-program-structure-results-assembly
kind: route
title: The structure theme is the conjunction of its member results
target: simple-kazhdan-lef-program-structure-results
requires:
  - subshift-elementary-group-properties-at-once
  - subshift-elementary-root-continuous-characters-are-trivial
  - simple-kazhdan-group-gives-property-t-factor-in-r-omega
  - full-group-word-problem-iff-recursive-language
  - subshift-elementary-groups-are-character-rigid
  - subshift-elementary-groups-have-trivial-irs
  - separable-factors-hold-countably-many-subshift-groups
  - cut-stabilizer-subgroups-of-el3-are-not-confined
  - elementary-root-subgroups-over-crossed-products-are-not-confined
  - locally-constant-gl-n-subgroup-is-not-confined
  - topological-full-group-images-in-el3-are-not-confined
  - cstar-simple-iff-amenable-subgroups-not-confined
  - nonamenable-rigid-stabilizers-give-cstar-simplicity
  - subshift-el-groups-vanishing-l2-betti-and-bounded-cohomology
  - no-amenable-normalish-subgroup-implies-cstar-simple
  - subshift-elementary-group-conjugacy-degree-is-jump
  - simple-kazhdan-lef-group-of-non-uniform-exponential-growth
  - nonsofic-leavitt-el4-non-uniform-exponential-growth
  - subshift-el-root-elements-boundedly-normally-generated
  - subshift-el3-has-continuum-many-maximal-subgroup-classes
  - subshift-el3-parabolic-subgroups-are-maximal
  - subshift-el3-orbit-stabilizers-conjugate-iff-same-orbit
  - subshift-el-groups-have-bounded-conjugation-invariant-norms
  - simple-amenable-group-of-non-uniform-exponential-growth
  - dyadic-tower-subshift-full-group-non-uniform-growth
  - subshift-el3-two-ended-lattice-stabilizers-locally-finite
  - unit-group-confined-subgroups-idempotent-commutator-lemma
  - idempotent-displacement-fails-for-polynomially-small-units
  - polynomially-small-units-have-order-dividing-420
  - laurent-linear-confining-sets-force-infinite-order-elements
  - banded-matrix-groups-are-subshift-crossed-product-groups
  - piecewise-dyadic-level-models-give-non-uniform-growth
  - matrix-decompositions-of-subshift-rings-need-divisible-unit
  - krieger-subshift-embedding-theorem
  - dyadic-derived-full-groups-no-uniform-semifree-diameter
  - whitehead-diagonal-map-is-not-multiplicative
---

Assembly only: the theme claim is the conjunction of the listed results. Each is proved or imported on its own route.

Members added by sk-cairn-steward-2 (2026-09-13, sk landings from 20:00 on): `subshift-elementary-groups-are-character-rigid` `subshift-elementary-groups-have-trivial-irs` `separable-factors-hold-countably-many-subshift-groups` `cut-stabilizer-subgroups-of-el3-are-not-confined` `elementary-root-subgroups-over-crossed-products-are-not-confined` `locally-constant-gl-n-subgroup-is-not-confined` `topological-full-group-images-in-el3-are-not-confined` `cstar-simple-iff-amenable-subgroups-not-confined` `nonamenable-rigid-stabilizers-give-cstar-simplicity`.

Members added by sk-cairn-steward-2 (2026-09-13, second pass, sk landings to 22:34): `subshift-el-groups-vanishing-l2-betti-and-bounded-cohomology` `no-amenable-normalish-subgroup-implies-cstar-simple` `subshift-elementary-group-conjugacy-degree-is-jump` `simple-kazhdan-lef-group-of-non-uniform-exponential-growth` `nonsofic-leavitt-el4-non-uniform-exponential-growth`.

Members added by sk-cairn-steward-2 (2026-09-13, third pass, sk landings to 22:47): `subshift-el-root-elements-boundedly-normally-generated` `subshift-el3-has-continuum-many-maximal-subgroup-classes` `subshift-el3-parabolic-subgroups-are-maximal`.

Members added by sk-cairn-steward-2 (2026-09-13, fourth pass, sk landings to 22:56): `subshift-el3-orbit-stabilizers-conjugate-iff-same-orbit` `subshift-el-groups-have-bounded-conjugation-invariant-norms`.

Members added by sk-cairn-steward-4 (2026-09-14, wave-12 sk landings): `dyadic-tower-subshift-full-group-non-uniform-growth`.

Members added by sk-cairn-steward-4 (2026-09-14, third pass): `polynomially-small-units-have-order-dividing-420` `laurent-linear-confining-sets-force-infinite-order-elements`.

Members added by sk-cairn-steward-5 (2026-09-14, wave-12 pass): `separable-factors-hold-countably-many-subshift-groups`, which revision 4.4 of the note no longer prints; `banded-matrix-groups-are-subshift-crossed-product-groups` `piecewise-dyadic-level-models-give-non-uniform-growth` `matrix-decompositions-of-subshift-rings-need-divisible-unit` `krieger-subshift-embedding-theorem` `dyadic-derived-full-groups-no-uniform-semifree-diameter`; and the firewall `whitehead-diagonal-map-is-not-multiplicative` (sk-subgroups), which shows that `X ↦ diag(X, X^-1)` is multiplicative only on commuting pairs and was unreachable before.
