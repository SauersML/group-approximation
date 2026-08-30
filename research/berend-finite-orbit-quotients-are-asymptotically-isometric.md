---
rg: 2
id: berend-finite-orbit-quotients-are-asymptotically-isometric
kind: claim
title: Finite-orbit quotients give asymptotically isometric decomposition-rank-two models of the Berend algebra
distinct_from:
  berend-proper-quotients-have-decomposition-rank-at-most-two: that bounds each proper quotient separately; this constructs one increasing sequence of such quotients which norms every element of the full algebra.
  stw99-lxxxvi-berend-groups-decomposition-rank: that asks for internal finite-colour completely positive approximations of the identity; asymptotically isometric quotient maps point in the opposite direction and do not by themselves bound decomposition rank.
artifacts:
  - research/artifacts/stw99-lxxxvi-berend-frontier-2026-08-30.md
---

Let `A = C(T^3) ⋊ Z^2` be Eckhardt's Berend crossed product.  There are
increasing finite invariant subsets `F_n subset T^3` and quotient maps

`q_n : A -> B_n := C(F_n) ⋊ Z^2`                           `(BFQ1)`

such that

`dr(B_n) <= 2`,  and  `lim_n ||q_n(a)|| = ||a||` for every `a in A`.
                                                                    `(BFQ2)`

Equivalently, the diagonal map gives an injective homomorphism

`A -> product_n B_n / direct_sum_n B_n`.                       `(BFQ3)`

This is an exact external approximation theorem for the faithful Berend
algebra, but it does not imply `dr(A) <= 2`.  Even commutative algebras of
arbitrarily large decomposition rank admit asymptotically isometric
quotient maps into finite-dimensional algebras.  A successful positive
proof for Berend must therefore add order-zero-compatible lifts back into
`A`, not merely improve the norm separation of its finite-orbit quotients.
