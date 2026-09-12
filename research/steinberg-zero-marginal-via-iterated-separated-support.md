---
rg: 2
id: steinberg-zero-marginal-via-iterated-separated-support
kind: route
title: Iterate the separated X summands until their shrinking supports vanish
target: steinberg-zero-marginal-fox-recurrence-is-zero
requires:
  - steinberg-x-row-splits-zero-marginal-tree-sectors
---

Starting from `F=T_1F+T_2F`, where

```text
T_1=A(1-q),                  T_2=B(1-s),
```

iterate the two outer-letter summands and attempt to obtain successively
more forbidden point and line fibers.  If support separation alone made the
forbidden set grow to every chord, this would prove the target without the
`Y` row.

This route is invalidated by
`steinberg-separated-support-imposes-only-matching-zeros`: the first split
has an exact codimension-`p` support content.  On further expansion the
individual words need not have separated tree support, so applying the first
split to each word is invalid; regrouping by the outer letter recovers only
the original two summands.
