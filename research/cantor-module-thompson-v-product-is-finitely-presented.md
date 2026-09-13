---
rg: 2
id: cantor-module-thompson-v-product-is-finitely-presented
kind: claim
title: The Cantor module C(C, F_2) extended by Thompson's V acting by precomposition is the centralizer of an involution in V and is of type F_infinity
distinct_from:
  leavitt-cantor-module-semidirect-product-is-fp: that is finite presentation of the extension by the whole binary Leavitt unit group, acting linearly on the module; this is the extension by Thompson's V alone, acting by permutations of clopen sets.
  orbit-finite-affine-actions-are-type-a: that is the criterion turning a finitely presented affine extension into a type (A) actor; this supplies one finitely presented extension.
artifacts:
  - research/artifacts/leavitt-module-fp-2026-09-13.md
---

**ESTABLISHED** through `cantor-module-thompson-v-product-fp-via-mmn-centralisers`
(2026-09-13, not independently reviewed). Part (i) is an elementary computation and
part (ii) is a literature import, checked against the source text.

## Statement

Let `C = {0,1}^N`, let `M = C(C, F_2)` be the additive group of locally constant
`F_2`-valued functions on `C`, and let Thompson's group `V` act on `C` by prefix
replacements and on `M` by `v · f = f ∘ v^(-1)`. Let `σ ∈ V` be the involution
`σ(a w) = (1-a) w`.

1. `C_V(σ) ≅ M ⋊ V`, with `V` acting on `M` as above.
2. `M ⋊ V` is of type `F_∞`; in particular it is finitely presented.

## Consumers

- `leavitt-cantor-module-fp-via-thompson-amalgam`: amalgamating this group with the
  binary Leavitt unit group over `V` gives finite presentation of the Leavitt Cantor
  module extension.

## Trust surface

- Martínez-Pérez–Matucci–Nucinkis, arXiv:1309.7858v2: Corollary 4.11, Theorem 4.2,
  Remark 4.3, Example 2.7(ii) and Definition 2.14, quoted verbatim in the artifact.
  The Brown-criterion proofs behind their Theorem 3.1 and Theorem 4.9 were not
  re-read.
- The reading that one colour of arity two is the Higman–Thompson group `V_(2,1) = V`,
  and that completeness (Definition 2.14) is vacuous for one colour.
