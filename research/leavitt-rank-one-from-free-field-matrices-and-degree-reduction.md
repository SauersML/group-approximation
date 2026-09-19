---
rg: 2
id: leavitt-rank-one-from-free-field-matrices-and-degree-reduction
kind: route
title: Move a commuting pair into the nonnegative part, read it as matrices over the free algebra, restrict to a minimal-rank image, and forbid a transcendence-degree-two subfield of matrices over the free field
target: leavitt-algebras-contain-no-two-variable-polynomial-ring
requires: [leavitt-polynomial-pairs-move-to-the-nonnegative-part, leavitt-nonnegative-part-is-matrix-union-over-free-algebra, matrices-over-free-fields-have-no-trdeg-two-subfields]
---

Fix a field `k` and suppose `a, b ∈ L_k(1,2)` commute and are algebraically independent over `k`.

1. **Move to one half.** By `leavitt-polynomial-pairs-move-to-the-nonnegative-part`, there is such a pair
   `a', b'` in `L_(>=0)`.
2. **Matrices over the free algebra.** By `leavitt-nonnegative-part-is-matrix-union-over-free-algebra`
   (Statements 1 and 2), `a', b'` lie in some `E_N ≅ M_(2^N)(k<x_0, x_1>)`, which sits inside `M_(2^N)(D)`.
   So `C = k[a', b'] ≅ k[x, y]` is a commutative domain there.
3. **Minimal-rank restriction.** By Statement 3 of the same claim, `M_r(D)` contains a subfield `F ≅ k(x, y)` for
   some `r <= 2^N`.
4. **Contradiction.** `trdeg_k F = 2` contradicts `matrices-over-free-fields-have-no-trdeg-two-subfields`. ∎

**Independence of the prerequisites.**
- Step 1 is about the Z-grading and the purely infinite part of `L`. It is untouched by skew-field theory.
- Step 4 is about stably finite matrix rings over a division ring. It does not involve `L` at all.
- If either one fails, the other can still hold.
- The step-4 claim is field-uniform, as the live need asks, and its case `r = 1` is a theorem.
