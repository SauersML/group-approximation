---
rg: 2
id: fpbs-burnside-upper-cost-one-via-normal-closure
kind: route
title: Apply the bounded-cost normal subgroup statement to the normal closure of one generator of B(m,n), m>=3
target: fpbs-burnside-upper-cost-one
requires:
  - fpbs-normal-subgroup-bounded-cost-fixed-price-one
  - fpbs-burnside-normal-closure-split
  - fpbs-burnside-common-upper-cost
artifacts:
  - research/artifacts/fpbs/docs/normal-subgroup-fixed-price.md
---

Consequence 3.2 of the linked note.

1. Fix odd `n` in the common range of the three premises and `m >= 3`. By
   `fpbs-burnside-normal-closure-split`, the normal closure `N` of one free
   generator of `B(m,n)` is infinite with infinite quotient `B(m-1,n)`.
2. By `fpbs-burnside-common-upper-cost`, every free p.m.p. action of `N`
   has cost at most `c_n <= 2 - 2/n`.
3. The open premise `fpbs-normal-subgroup-bounded-cost-fixed-price-one` then
   gives fixed price one for `B(m,n)`, so `C*(B(m,n)) = 1`.
4. The common-upper-cost theorem identifies `c_n` with `C*(B(m,n))`. Hence
   `c_n = 1`, and every infinite subgroup of every `B(m',n)`, including
   `B(2,n)`, has upper cost one.

The only open premise is the per-action normal subgroup statement. This route
decides the Burnside branch positively: together with
`fpbs-burnside-explicit-action-pair` it excludes `c_n > 1`, which is what
`fpbs-burnside-positive-upper-cost` asks for.
