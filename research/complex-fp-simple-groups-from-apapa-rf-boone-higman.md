---
rg: 2
id: complex-fp-simple-groups-from-apapa-rf-boone-higman
kind: route
title: Embed the hard Kharlampovich-Myasnikov-Sapir groups of the variety A_p^2 A and read off complex simple hosts
target: fp-simple-groups-with-arbitrarily-complex-word-problem
requires:
  - fp-rf-apapa-groups-satisfy-boone-higman
  - kms-hard-fp-rf-groups-lie-in-apapa-variety
artifacts:
  - research/artifacts/bh-complex-wp-apapa-reduction-2026-09-13.md
---

Fix a recursive `T: N -> N` and put `T+(m) = m + max_(k<=m) T(k)`, which is
recursive, non-decreasing and at least `T`. Write `F(g)` as in `(KMS2)` of
`kms-arbitrarily-hard-fp-rf-groups`.

1. **A hard recursive problem.** Step 1 of
   `uniform-wp-bound-excludes-bh-targets-proof`, run with `g = T+`, gives a
   recursive problem `X` outside `F(T+)` by a clocked diagonalization.
2. **A hard group in the variety.** By
   `kms-hard-fp-rf-groups-lie-in-apapa-variety`, there are a prime `p` and a
   finitely presented residually finite group `G` in `A_p^2 A` such that any
   time-`T_G` word-problem algorithm for `G` gives an algorithm for `X` in time
   `C*T_G(C*n) + C*n + C`. If the word problem of `G` were in `F(T+)`, then `X`
   would be in `F(T+)`, by the closure statement `(KMS2)`. So the word problem of
   `G` is not in `F(T+)`.
3. **The host.** By `fp-rf-apapa-groups-satisfy-boone-higman`, `G <= S` for some
   finitely presented simple group `S`.
4. **Transfer.** Suppose `S` had a word-problem algorithm in time
   `C_S*T(C_S*l) + C_S*l + C_S` over some finite generating set. Write the
   generators of `G` as words of length at most `L` over it. A word of length `l`
   over `G` becomes, in time `O(L*l)`, a word of length at most `L*l` over `S`,
   trivial iff the original is. That decides the word problem of `G` in time at
   most `C'*T+(C'*l) + C'*l + C'` for a constant `C'`, using monotonicity of `T+`
   and `T <= T+`. This contradicts step 2.

So `S` beats `T`. The embedding need not be effective: `L` is a constant once a
generating set is chosen. This is the substitution of
`complexity-bounded-host-classes-are-not-universal-proof`. `∎`
