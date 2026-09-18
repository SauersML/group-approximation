---
rg: 2
id: abstract-btb-pairs-fp-via-colored-stein-complex
kind: route
title: Take finite presentation from the colored-Stein-complex criterion instead of FFWZ Theorem B(ii), and import relative simplicity and the pair embedding
target: abstract-btb-pairs-fp-and-relatively-simple
requires:
  - abstract-twisted-bt-type-fn-criterion
---

This is a second derivation of `abstract-btb-pairs-fp-and-relatively-simple`. The first, the
citation route, imports item 1 from FFWZ Theorem 4.1(ii). For non-faithful actions the
published proof of that item has the gap recorded in
`ffwz-nonfaithful-stein-stabilizers-contain-canonical-kernel`. This route avoids it.

- **Item 1 (finite presentation).** For a type `[A_2]` action, `SV_G` is finitely presented
  by `abstract-twisted-bt-type-fn-criterion`, item 2. That proof runs the Stein-complex
  argument on the `S`-colored subgroup of the faithful `(S ⊔ G)V_G`.
- **Item 2 (relative simplicity).** Imported from FFWZ, arXiv:2603.24687v2, Theorem 3.6
  (text lines 667–670 of `/scratch.global/sauer354/bh-reviewer/2603.24687.txt`): "Let G be a
  group acting on a non-empty set S. The abstract twisted Brin–Thompson group SV_G is
  relatively simple, with largest normal subgroup the canonical kernel SK_G." The proof (§3)
  does not use the Stein complex.
- **Item 3 (pair embedding).** Imported from FFWZ Lemma 5.2 (text line 1204 onward): "Let
  G ↷ S be a group action with kernel K. Then the normal pair (G,K) sharply embeds in
  SV_G." The proof sends `g` to `[·, id, g, ·]`.

Items 2 and 3 hold for every action. Item 1 uses type `[A_2]`.
