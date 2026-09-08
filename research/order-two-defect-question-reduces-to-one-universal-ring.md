---
rg: 2
id: order-two-defect-question-reduces-to-one-universal-ring
kind: claim
title: The whole additive-order-two question is equivalent to marked collapse over one explicit ring
distinct_from:
  order-two-universal-ring-has-finitary-symbol-sequence: that is the ring and group structure of the universal order-two ring; this is the three-way equivalence between the class question, non-MF of its elementary group, and collapse of one named root there.
  finite-additive-order-one-sided-defects-are-mf-invisible: that answers the class question affirmatively for every finite additive order, at rank four and above, using property (T); this is a rank-preserving equivalence valid at every fixed rank at least two, and asserts nothing about which side holds.
  prime-characteristic-defect-embeds-the-jacobson-algebra: that reduces the characteristic-p class to one ring by a ring embedding; this reduces the additive-order-two class, which contains rings of characteristic zero, and the reduction is not by an embedding.
artifacts:
  - research/artifacts/fullness-corner-and-order-two-reduction-2026-09-08.md
---

**ESTABLISHED.**  Fix `n >= 2` and let `A_2 = Z<S,T | TS = 1, 2Q = 0>` be
the ring of `order-two-universal-ring-has-finitary-symbol-sequence`, with
`Q = 1 - ST` and `w = e_12(Q)`.  The following are equivalent.

1. For every countable unital ring `R` with `ts = 1` and `1 - st` of
   additive order two, `EL_n(R)` is non-MF.
2. `EL_n(A_2)` is non-MF.
3. Every homomorphism from `EL_n(A_2)` to an MF group kills `w`.

When they hold, every homomorphism from every group in statement 1 to an
MF group kills the corresponding `e_12(1-st)` — a **named** element, not
merely some unspecified nonidentity one.

**Where the content is.**  Statement 2 implies statement 3 is the
substantive step.  Non-MF of a universal group does not ordinarily give
marked collapse in it; here it does, because the symbol kernel `L_n` of
`(OT4)` is simple, so a homomorphism retaining `w` is injective on `L_n`,
and pairing it with the symbol map embeds `EL_n(A_2)` into a product of
two MF groups.

**Current status of the equivalent statements.**  Statement 1 is
established for every `n >= 4` by
`finite-additive-order-one-sided-defects-are-mf-invisible`, so all three
hold there.  At `n = 2` and `n = 3` they are open together; that is
`order-two-universal-non-mf-at-ranks-two-and-three`.  The standing rank
descent `elementary-rank-descent-to-two` does not close the gap, because
it needs a properly infinite unit and
`order-two-universal-ring-has-no-infinite-corner` shows `A_2` has none,
in any finite matrix amplification.

This node is a reduction.  It proves none of its three statements.

DERIVATION
order-two-universal-reduction-proof
