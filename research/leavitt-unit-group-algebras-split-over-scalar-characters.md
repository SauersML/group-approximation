---
rg: 2
id: leavitt-unit-group-algebras-split-over-scalar-characters
kind: claim
title: Every finite-field Leavitt unit group algebra splits over its scalar characters, and the Leavitt evaluation sees exactly one factor
distinct_from:
  ternary-leavitt-swap-problem-splits-at-central-involution: that is the case q = 3, where the scalars are plus and minus one, together with the swap corner and its Cohn reformulation; this is the splitting for every prime power q and every arity d, with q - 1 factors, the Leavitt-visible factor identified, and the augmentation behaviour recorded.
artifacts:
  - research/artifacts/leavitt-host-survey-scalar-characters-2026-09-12.md
---

Let `q = p^r`, `d >= 2`, `L = L_(F_q)(1,d)`, `G = L^x`, `A = F_q[G]` and `pi : A -> L` the evaluation.
The scalars `Z = F_q^x . 1` form a central cyclic subgroup of `G` of order `q - 1`. For each character
`chi : Z -> F_q^x` put `eps_chi = (1/(q-1)) sum_lambda chi(lambda)^(-1) [lambda]`.

1. The `eps_chi` are central orthogonal idempotents with sum `1`, so `A = prod_chi A_chi`, and
   `[lambda]` acts as `chi(lambda)` on `A_chi`.
2. `pi(eps_chi) = 1` for `chi = iota` (`iota(lambda) = lambda`) and `0` otherwise. So `pi` factors
   through the Leavitt-visible factor `A_iota`.
3. The trivial-character factor is `F_q[G/Z]`.
4. A one-sided pair `c a = eps_chi != a c` in any single factor, padded by `1 - eps_chi`, is a
   one-sided pair of `A`. So `A` is not directly finite.
5. For `q > 2` the augmentation vanishes on `A_iota`. For `q = 2` there is one factor, and the
   augmentation is visible on it.

ESTABLISHED by `leavitt-scalar-character-splitting-proof` (Section 1 of the artifact).
