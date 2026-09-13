---
rg: 2
id: braid-group-contains-z2-by-nonamenable-sl2z-subgroup
kind: claim
title: Some braid group contains Z^2 extended by a non-amenable group acting through SL_2(Z)
refuted_by: braid-abelian-normalizer-actions-are-virtually-solvable
distinct_from:
  braid-abelian-normalizer-actions-are-virtually-solvable: that claim is an established theorem implying the negation of this one
  some-braid-group-lacks-the-haagerup-property: that claim is the failure of the Haagerup property; this is one hypothetical source of that failure
---

There are `n`, a subgroup `A ≅ Z^2` of `B_n`, and a subgroup `Γ ≤ B_n` normalizing `A`, such that the
conjugation action `Γ → GL(A) ≅ GL_2(Z)` has non-amenable image inside `SL_2(Z)`.

If true, `B_n` would contain a Burger pair and fail the Haagerup property. It is false:
`braid-abelian-normalizer-actions-are-virtually-solvable` shows the image is always virtually solvable.

## Attempts

- Refuted (z3-07-braid-haagerup, 2026-09-13): a bi-order of `P_n` restricted to `A ∩ P_n` is invariant under
  `Γ ∩ P_n`, and order-preserving actions on `Z^k` have solvable image.
