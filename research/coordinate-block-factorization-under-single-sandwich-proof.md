---
rg: 2
id: coordinate-block-factorization-under-single-sandwich-proof
kind: route
title: Sandwich the pivot entry, clear the row and the column, and read the word length off the two sweeps
target: coordinate-block-factorization-under-single-sandwich
requires: []
artifacts:
  - GroupApproximation/PropertyTT/MatrixElimination.lean
  - GroupApproximation/PropertyTT/CoordinateBlocks.lean
  - GroupApproximation/PropertyTT/BoundedGeneration.lean
  - GroupApproximation/PropertyTT/RingHypotheses.lean
---

## Direct proof, machine-checked

No prerequisite: `HasSingleSandwichDivision` (`PropertyTT/RingHypotheses`) is
the only hypothesis besides invertibility, and every step below is a finite
matrix calculation.

**The pivot, in three moves** (`exists_three_move_diagonal_pivot`).  Fix
distinct coordinates `i != j`.  If `A_ii = 0`, invertibility supplies `k` with
`A_ik != 0`, so one column operation `e_ki(1)` makes the `(i,i)` entry nonzero;
write `A^(0) = A F_0` and `a = A^(0)_ii != 0`, `b = A^(0)_ij`.  Choose the
sandwich `p a q = 1` and set

    rho = q(1 - p b),   F_1 = e_ij(rho),   A_1 = A^(0) F_1,   b_1 = (A_1)_ij .

Then `b_1 = a rho + b` and `p b_1 = p a q (1 - p b) + p b = 1`: the sandwich is
spent making the `(i,j)` entry *left-invertible by the fixed element `p`*, not
invertible.  That one-sided inverse is enough, because the last move is a row
operation.  With `d_1 = (A_1)_jj` and `w = (1 - d_1) p`,

    (e_ji(w) A_1)_jj = d_1 + w b_1 = d_1 + (1 - d_1) p b_1 = 1 .

One left factor, at most two right factors, arbitrary ring.

**The two sweeps** (`rightClearFactors_clear_row`,
`leftClearFactors_make_coordinateBlock`).  With a literal `1` at `(j,j)`,
right-multiplying by `e_jk(-B_jk)` for each of the `n-1` coordinates `k != j`
clears row `j`: the factors share the source column `j` and have distinct
target columns, so each leaves the previously cleared entries at zero, and the
entry it targets becomes `B_jk + B_jj(-B_jk) = 0`.  Left-multiplying by
`e_kj(-C_kj)` for each `k != j` clears column `j` by the same disjointness
argument, and the result `D` fixes `e_j` and `e_j^t`, i.e. `D` lies in the
coordinate block.  Each sweep is exactly `n-1` factors.

**The word** (`boundedProduct_coordinateBlockOrRoot`).  Solving `D = S E A F T`
gives `A = E^(-1) S^(-1) D T^(-1) F^(-1)`; inverse products reverse the factor
lists and `e_ab(z)^(-1) = e_ab(-z)` keeps every factor elementary, so the
factorization has the exact shape

    l_rev^(-1) . s_rev^(-1) . [D] . t_rev^(-1) . r_rev^(-1)

of length at most `1 + (n-1) + 1 + (n-1) + 2 = 2n+2`, with the single block
letter in the middle.  Since `j` never entered the pivot choice, it may be
fixed before `A` is given, which is the form
`coordinateBlock_factorization` states.

## Why no stable-range input appears

The usual bounded-generation proof shortens the word using a stable-range
condition, which is unavailable here -- the intended coefficient rings have
infinite Bass stable rank.  The sandwich replaces it pointwise: it is applied
once, to the single entry `a`, and the resulting `p` is reused as the
multiplier of the row move.  That is the whole reason the constant is uniform
in the ring and linear in `n`.
