---
rg: 2
id: free-minimal-fn-cantor-action-not-almost-unperforated
kind: claim
title: Some free group of finite rank at least 2 acts freely and minimally on the Cantor space with a type semigroup that is not almost unperforated
distinct_from:
  free-minimal-cantor-action-with-finite-clopen-type: that allows any countable group but demands no invariant measure and a finite clopen class; this demands a finitely generated free group and only a failure of almost unperforation.
---

For some `n` with `2 <= n < infinity` there is a free minimal action of `F_n`
on a Cantor space `X` such that `S(X, F_n)` is not almost unperforated.

By `induced-cantor-action-type-semigroup-matches-subgroup` this is equivalent
in strength, for the purpose of Rainone's question, to the case `n = 2`
(`rainone-free-minimal-f2-action-not-almost-unperforated`): the rank is a free
parameter that a construction may choose.

## Attempts

* **More letters.**  A larger finite rank gives more generators to carry
  finitely many prescribed values in a Baire argument.  Where it dies: the
  obstruction recorded on
  `rainone-free-minimal-f2-action-not-almost-unperforated` (tuples preserving
  a common clopen set form a nonempty open set with no exhaustive member)
  holds for every finite rank.  Infinitely many requirements still have to be
  carried by finitely many letters.
