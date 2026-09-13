---
rg: 2
id: el-n-mf-quotient-below-twice-paradoxical-level-exists
kind: claim
title: Some ring of paradoxical level p >= 2 has an elementary group EL_N, 3 <= N < 2p, with a nontrivial homomorphism to an MF group
distinct_from:
  paradoxical-ring-el-n-full-mf-radical-from-twice-level: that proves full MF radical from rank 2p; this asks whether the band between rank 3 and rank 2p is genuinely different.
  non-ibn-ring-el-n-full-mf-radical-above-module-rank: that kills the band above rank m for rings with an exact failure of IBN; this asks about what remains.
---

There is a countable unital ring `R`, finitely generated, with paradoxical level `p(R) = min{n : (n+1)[R] ≤ n[R]} ≥ 2`,
and some `N` with `3 ≤ N < 2p(R)`, such that `EL_N(R)` has a nontrivial homomorphism to an MF group.

If true, this gives a new object: a finitely generated Kazhdan group `EL_N(R)` with a nontrivial MF quotient sitting
inside `EL_{2p}(R)`, which has none. If false, it strengthens
`paradoxical-ring-el-n-full-mf-radical-from-twice-level` below rank `2p`.

## Attempts

- **Candidate `R = L_k(2,3)`, `N = 3`: dead.** `non-ibn-ring-el-n-full-mf-radical-above-module-rank` gives full MF radical
  of `EL_N(L_k(2,3))` for all `N ≥ 3`, by conjugating `EL_{N+j}` into `EL_N` through `R^2 ≅ R^3`, using a free
  coordinate.
- **What is left for module type `(m, m+d)`: `3 ≤ N ≤ m`.** Simplest case: `EL_3(L_k(3,4))`.
  - With no free coordinate, `Φ(e_ij(r)) = 1 + x_i r y_j` (`y_j x_i = 0`) is not visibly elementary.
  - Recalled (Bergman): `R^i ≅ R^j` only for `i = j` or `i, j ≥ m`, so no smaller exact isomorphism exists.
  - Membership of such transvections in `E_3` is a normality question over a noncommutative ring. `E_n` need not be
    normal in `GL_n` (Gerasimov, recalled).
- **Paradoxical rings without exact IBN failure** (`R^n ≅ R^{n+1} ⊕ Q` with `Q` not stably free): the conjugation trick
  needs an exact isomorphism with a free coordinate. The band `3 ≤ N < 2p` stands there.
- **Printed transport is silent below the thresholds.** No `M_j(R)` with `2j ≤ N < 2p` has a one-sided inverse with
  full complement, since that would make `[R]` paradoxical at level `j < p`.
- **Ring approximations are dead.** Paradoxical `[R]` means no state at `[R]`, hence no normalized Sylvester rank
  function and no unital embedding into a matrix ultraproduct. An MF quotient would have to come from approximations
  that are not ring homomorphisms.
