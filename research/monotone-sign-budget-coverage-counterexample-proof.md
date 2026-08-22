---
rg: 2
id: monotone-sign-budget-coverage-counterexample-proof
kind: route
title: Put one Pauli odd block at each central atom and reset them one at a time
target: monotone-anchor-sign-budget-does-not-give-stagewise-coverage
requires:
  - odd-spectral-anchor-resets-have-monotone-sign-budget
---

On block `i`, `Z X Z=-X`, so `Y_i=X`; on every other block `B_i=A=Z`,
so `Y_i=0`.  This proves `(MCV2)`.  The projections `z_i` are central and
therefore have zero boundary.

Resetting `A` on blocks in `J` replaces `Z` by `1` there.  This makes every
odd part vanish on those blocks.  It does not change block `i notin J`,
where the pair remains `(Z,X)`, proving `(MCV3)`.  The normalized negative
trace of `Z` is one half on every block, which proves `(MCV4)`.

Finally `[Z,X]=2ZX` has normalized squared Hilbert--Schmidt norm `4` in
`M_2`.  The pair `(B_i,B_j)` anticommutes on exactly two blocks and commutes
elsewhere, giving `(MCV5)`.  Summing the ordered pairs and dividing by
`(N+1)^2` gives `O(1/N)`.  All assertions are exact.

