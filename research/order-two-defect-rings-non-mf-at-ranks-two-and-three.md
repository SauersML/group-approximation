---
rg: 2
id: order-two-defect-rings-non-mf-at-ranks-two-and-three
kind: claim
root: true
title: Decide the additive-order-two class question in ranks two and three
distinct_from:
  finite-additive-order-one-sided-defects-are-mf-invisible: that settles every finite additive order at every rank at least four; this is the residue of the same class question at ranks two and three.
  order-two-universal-non-mf-at-ranks-two-and-three: that is the single universal ring; this is the whole class, which the reduction shows the universal ring controls.
  full-defect-ring-non-mf-at-rank-two: that reaches rank two under ambient fullness, which fails for a torsion defect since a full defect cannot survive in a nonzero commutative quotient; this is the fullness-free torsion class at the same ranks.
artifacts:
  - research/artifacts/fullness-corner-and-order-two-reduction-2026-09-08.md
---

For `n in {2,3}`, decide whether every countable unital ring `R` carrying
`s,t` with

```text
ts = 1,      1 - st != 0,      2(1 - st) = 0                      (OTC1)
```
has `EL_n(R)` non-MF, and whether every MF-target homomorphism kills the
named root `e_12(1-st)`.

By `order-two-defect-question-reduces-to-one-universal-ring` this is
equivalent, at each such `n` separately, to the single-ring question
`order-two-universal-non-mf-at-ranks-two-and-three`, and the marked form
follows from the plain one.  For `n >= 4` the answer is affirmative, by
`finite-additive-order-one-sided-defects-are-mf-invisible`.

## Attempts

Every attempt recorded on the universal-ring node applies here through
the reduction, and there is no known attack on the class that does not
factor through it: the reduction is exact, so a class counterexample and
a counterexample over `A_2` are the same object.

One class-level attempt that is specific to this node and dies quickly:
restricting to rings of characteristic two, where
`prime-characteristic-defect-embeds-the-jacobson-algebra` embeds
`J_(F_2)` and would let the binary Jacobson answer transport.  That
does not reach the class, because `(OTC1)` allows characteristic zero —
`A_2` itself is the witness — and
`binary-jacobson-mf-implies-order-two-universal-mf` shows the transport
between the two rings runs in the unhelpful direction.
