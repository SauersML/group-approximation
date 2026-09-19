---
rg: 2
id: tracial-to-uniform-lifting-for-sl-n-z
kind: claim
title: Some higher-rank integral lattice admits uniform operator approximants after negligible padding
artifacts:
  - research/artifacts/operator-lift-ulam-quantifier-audit-2026-09-05.md
distinct_from:
  sln-z-flexibly-hs-stable: that asks directly for exact padded representations; this asks for nearby maps with an operator-norm multiplicative bound uniform over all group pairs, which the published Ulam theorem can then correct.
  bounded-degree-two-primitives-for-higher-rank-lattices: that concerns additive cochain bounds; this requires global multiplicative control on actual group maps and includes a dimension ledger.
---

OPEN CLAIM. For some `N>=3`, put `G=SL_N(Z)` and fix a finite
presentation `<S|R>`. Every sequence of generator tuples
`U_j:S->U(d_j)` with normalized-HS defining defect tending to zero
admits dimensions `D_j>=d_j` and unital maps `f_j:G->U(D_j)` such that

```text
(D_j-d_j)/d_j -> 0,
max_(s in S)||f_j(bar(s))-(U_j(s) direct_sum I_(D_j-d_j))||_(2,D_j)
 -> 0,
eta_j := sup_(g,h in G)||f_j(gh)-f_j(g)f_j(h)||_op -> 0.       (TUL1)
```

The supremum is taken before the limit. It is part of the open
hypothesis, not a consequence of small errors on fixed relators.
For each fixed N, this property is equivalent to flexible HS stability:
the Ulam theorem corrects `(TUL1)`, and an exact flexible correction
itself supplies maps with `eta_j=0`.

This formulation replaces the earlier, insufficient operator-ultraproduct
lifting statement. A homomorphism into an operator-norm ultraproduct
only makes the defect vanish for each fixed pair; it does not provide
`(TUL1)`. Also, deleting a vanishing corner and exactly correcting the
remaining tuple would give same-dimension correction after filling the
corner with the trivial representation. Genuine dimension addition is
allowed here and cannot be replaced by that deletion convention.

## Attempts

- **The Ulam theorem is applicable once the stated input exists.**
  Burger--Ozawa--Thom, *On Ulam stability*, Section 2 and Theorem 1.3,
  use the supremum over all group pairs in defining defect. Their
  finite-dimensional stability modulus for `SL_N(Z)` is independent
  of matrix dimension. See [the primary paper](https://arxiv.org/abs/1010.0565).
  The broader higher-rank results in [Glebsky--Lubotzky--Monod--Rangarajan](https://arxiv.org/abs/2301.00476)
  also concern uniform stability. Neither citation supplies the open
  conversion from defining-relator HS defect to `(TUL1)`.
- **What the new cohomology theorem gives.**
  `two-kazhdan-correction-has-quadratic-rank-curvature` gives uniform
  fixed-tolerance concentration of defining errors at quadratic rank.
  Even its operator-small input case improves only fixed relator or
  fixed-pair errors. It supplies neither the all-pairs supremum nor the
  dimension-adding correction required here.
- **Column gluing remains obstructed.**
  `exact-levi-affine-relative-stability-fails` rules out a universal
  column-repair method that keeps its Levi representation exact. It
  does not decide `(TUL1)`, which allows all generators to change.
- **The former equivalence was not proved.**
  The audit artifact gives an elementary moving-spike counterexample
  to the interchange of the two quantifiers and explains the mistaken
  corner convention. Pointwise operator lifting, by itself, remains
  insufficient for the cited proof. This node now exposes the stronger
  input actually used, rather than labeling it as supplied by lifting.
