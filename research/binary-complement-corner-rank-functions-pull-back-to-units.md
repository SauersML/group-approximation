---
rg: 2
id: binary-complement-corner-rank-functions-pull-back-to-units
kind: claim
title: Normalized rank functions on the binary complement corner are exactly the non-augmentation rank functions on F_2[R^x]
distinct_from:
  simple-group-rank-functions-are-augmentation-or-detecting: that is the dichotomy for one rank function on a simple group algebra; this transports rank functions between the group algebra and the augmentation-free corner (1 - e) F_2[R^x] (1 - e) through the halving homomorphism, in both directions.
  binary-leavitt-units-carry-nonaugmentation-rank-function: that is the open existence claim on the group algebra; this is an established equivalence moving it to the complement corner.
artifacts:
  - research/artifacts/binary-cyclic-corner-complement-states-2026-09-12.md
---

**ESTABLISHED** (on paper, lane `w5-binary-upg`; verification requested from `w4-vf-linear-b`) by
`binary-complement-corner-rank-pullback-proof`.

Let `R = L_(F_2)(1,2)` and `G = R^x`, with `g`, `e = 1 + [g] + [g²]` and `f = 1 - e` as in
`binary-cyclic-corner-full-iff-complement-corner-has-no-state`. Put `T = f F_2[G] f` and
`D(h) = Σ s_i h t_i` (ternary family).
- If `N` is a Sylvester matrix rank function on `T` with `N(f) = 1`, then `N(f D(·))` is a Sylvester matrix
  rank function on `F_2[G]` with `rk(1 - [g]) = 2/3`. It detects every nontrivial element.
- If `rk` is a Sylvester matrix rank function on `F_2[G]` other than the augmentation rank, then
  `rk(f) > 0`, and `rk/rk(f)` restricts to a normalized Sylvester matrix rank function on `T`.

So `binary-leavitt-units-carry-nonaugmentation-rank-function` holds iff `T` carries a normalized Sylvester
matrix rank function.

**Consequences** (artifact Section 3 and Corollary 4.2).
- **The Sylvester two-root gate moves to `T`.** `sylvester-rank-functions-on-leavitt-units-kill-two-root-defect`
  is equivalent to `T` having no normalized rank function.
- **No division rings.** `T` has no unital homomorphism into `M_n(D)` for any division ring `D` of
  characteristic two.

## Attempts

Established, not open. Proof in artifact Section 3.
