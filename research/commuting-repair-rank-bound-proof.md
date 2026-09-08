---
rg: 2
id: commuting-repair-rank-bound-proof
kind: route
title: Expand the uncorrected commutator through the corrected one and count rank, then exhibit the block repair
target: commuting-repair-forces-half-dimension-rank
requires: []
artifacts:
  - research/artifacts/retained-core-and-rank-countertests-2026-09-08.md
---

## Proof

**The defect.**  `U V e_j = zeta^(j+1) e_(j+1)` and `V U e_j = zeta^j e_(j+1)`,
so `U V = zeta V U` and `U V U^* V^* = zeta I`, giving `(CR1)`.

**The rank bound.**  Put `Delta_U = U_0 - U^`, `Delta_V = V_0 - V^`.  Using
`U^ V^ = V^ U^`,

```text
U_0 V_0 - V_0 U_0
  = (U_0 V_0 - U^ V^) - (V_0 U_0 - V^ U^)
  = Delta_U V_0 + U^ Delta_V - Delta_V U_0 - V^ Delta_U.
```

The right side is a sum of four terms, each of rank at most
`rank(Delta_U)` or `rank(Delta_V)`, so its rank is at most
`2 rank(Delta_U) + 2 rank(Delta_V)`.  The left side is
`(U V - V U) (+) (A B - B A) = (zeta - 1) V U (+) (A B - B A)`, and
`(zeta - 1) V U` is invertible on the first summand because `zeta != 1` for
`d >= 2`; hence the left side has rank at least `d`.  Comparing gives `(CR2)`.

For the exponential form, `exp(i K) U_0 - U_0 = (exp(i K) - 1) U_0` has the
rank of `exp(i K) - 1`, which is at most `rank(K)`; a `K` with only
old-to-new off-diagonal blocks has rank at most `2k`.  Then `(CR2)` reads
`4k >= d / 2`.

**The repair.**  Let `d = q^3` and index the cycle by
`j = a q^2 + b` with `0 <= a < q`, `0 <= b < q^2`.  Define
`U' e_j = zeta^(a q^2) e_j` and `V' e_(a q^2 + b) = e_(a q^2 + (b + 1 mod q^2))`.
Each block `{a q^2, ..., a q^2 + q^2 - 1}` is invariant under both, `U'` is a
scalar there and `V'` a cyclic permutation, so `U' V' = V' U'`.  Both are
unitary.

For the estimates: on the block containing `j`, the clock phases differ by an
angle at most `2 pi q^2 / d = 2 pi / q`, so
`|U_(jj) - U'_(jj)| <= 2 pi / q` for every `j` and
`||U - U'||_(2,d) <= 2 pi / q`.  The columns where `V` and `V'` differ are
exactly the `q` block-final indices; each changes from one standard basis
vector to another, contributing squared norm `2`, so
`||V - V'||_(2,d)^2 = 2 q / q^3` and `||V - V'||_(2,d) = sqrt 2 / q`.
Finally `U - U'` vanishes exactly at the `q` block-initial indices, so its rank
is `d - q`.
