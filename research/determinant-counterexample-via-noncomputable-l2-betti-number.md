---
rg: 2
id: determinant-counterexample-via-noncomputable-l2-betti-number
kind: route
title: A noncomputable kernel dimension over a decidable group violates the determinant conjecture
target: determinant-conjecture-counterexample-exists
requires: [decidable-group-with-noncomputable-l2-betti-number, decidable-groups-have-right-computable-l2-betti-numbers]
---

Let `G` be decidable, and let `T` over `Q[G]` have noncomputable `dim_vN ker T`. If `G`
satisfied the determinant conjecture, part 2 of
`decidable-groups-have-right-computable-l2-betti-numbers` would make that dimension computable.
So some integral matrix over `G`, namely `N T`, has Fuglede--Kadison determinant below one.

This is the contrapositive of Löh--Uschold, arXiv:2202.03159, Theorem 1.2, in Turing degree 0.
