---
rg: 2
id: el-n-mf-quotient-below-twice-paradoxical-level-exists
kind: claim
title: Some ring of paradoxical level p >= 2 has an elementary group EL_N, 3 <= N < 2p, with a nontrivial homomorphism to an MF group
distinct_from:
  paradoxical-ring-el-n-full-mf-radical-from-twice-level: that proves full MF radical from rank 2p; this asks whether the band between rank 3 and rank 2p is genuinely different.
---

There is a countable unital ring `R`, finitely generated, with paradoxical level `p(R) = min{n : (n+1)[R] ≤ n[R]} ≥ 2`,
and some `N` with `3 ≤ N < 2p(R)`, such that `EL_N(R)` has a nontrivial homomorphism to an MF group.

If true, this gives a new object: a finitely generated Kazhdan group `EL_N(R)` with a nontrivial MF quotient sitting
inside `EL_{2p}(R)`, which has none. If false, it strengthens
`paradoxical-ring-el-n-full-mf-radical-from-twice-level` below rank `2p`.

## Attempts

- **Candidate `R = L_k(2,3)`, `N = 3`.** Cohn's theorem (recalled, not verified) makes `L(m,n)` with `m ≥ 2` an
  `(m−1)`-fir, so `L(2,3)` is a domain, directly finite, of level 2. `EL_4(L_k(2,3))` has full MF radical.
- **Printed transport is silent below `2p`.** No `M_j(R)` with `2j ≤ N` has a one-sided inverse with full complement (a
  full complement would make `[R]` paradoxical at level `j < p`). So no block copy of `thm:full-defect-ring` fits
  inside `EL_N(R)`.
- **Ring approximations are dead.** Paradoxical `[R]` means no state at `[R]`, hence no normalized Sylvester rank
  function and no unital embedding into a matrix ultraproduct. An MF quotient would have to come from approximations
  that are not ring homomorphisms.
- **Module-isomorphism route (where it stands).** `R^3 ≅ R^4` gives a group isomorphism `Φ : GL_4(R) → GL_3(R)`,
  `g ↦ AgB`, with `Φ(e_ij(r)) = 1 + a_i r b_j` and `b_j a_i = 0`. If some such transvection with full ideal lies in
  `EL_3(R)`, then `EL_3(R)` has full MF radical and the claim fails for `N = 3`. Membership is a normality question for
  `E_3` in `GL_3` over a noncommutative ring. `E_n` need not be normal there (Gerasimov, recalled), so it is not
  automatic.
