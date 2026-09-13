---
rg: 2
id: random-complex-bounded-removals-have-no-quotients-below-exp-pn
kind: claim
title: Removing any bounded set of triangles from a Linial--Meshulam complex leaves no nontrivial finite quotient of order at most exp(pn/8)
distinct_from:
  random-complex-group-no-quotients-below-exp-pn: that is the case t = 0, quotients of π_1(Y) itself; this holds simultaneously for π_1(Y \ T) over every set T of at most t triangles of Y, and those quotients need not factor through π_1(Y)
  random-complex-bounded-removal-detected-by-quotient: that is the open claim that some bounded removal has a finite quotient detecting a removed perimeter; this proves that every such quotient, for every choice of T at once, has order above exp(pn/8)
  bounded-removal-finite-quotient-caps-cocycle-cheeger: that turns a detecting quotient into a cap on the cocycle Cheeger constant; this bounds the order of any detecting quotient from below
---

**ESTABLISHED.** Fix an integer `t >= 0`. Let `Y ~ Y(n,p)` be the
Linial--Meshulam complex: complete 1-skeleton on `n` vertices, each triangle
present independently with probability `p`. Suppose `pn >= 30 log n` (natural
logarithm). Then a.a.s. the following holds simultaneously for every
`T ⊂ Y(2)` with `|T| <= t`:

> `π_1(Y \ T)` has no nontrivial finite quotient of order at most `exp(pn/8)`.

Here `Y \ T` is the 2-complex with 1-skeleton `K_n` and triangles `Y(2) \ T`.

Derivation: `random-complex-bounded-removals-no-small-quotients-proof`.
Nothing new is claimed. It is Meshulam's first moment with a binomial tail.

## Mid-range form

For `p = n^(-1+η)` with `0 < η < 1`, a.a.s. for every `T ⊂ Y(2)` with `|T| <= t`,
every nontrivial finite quotient of `π_1(Y \ T)` has order above `exp(n^η/8)`.

In `random-complex-bounded-removal-detected-by-quotient`, a detecting quotient
has nontrivial image. So every detecting quotient, for every admissible `T`, has
order above `exp(n^η/8)`.

## What it settles

The detection node said: "Whether the exclusion holds for all `n^(O(t))` choices
of `T` at once is not checked." It does, with a larger order bound than
Meshulam's polynomial one. The union over `T` is absorbed into a binomial tail
and costs a factor `(pn)^t`, against `exp(-pn/12)`.

The first-moment ceiling recorded on `random-complex-group-no-quotients-above-exp-pn`
applies here as well. Removing triangles only adds violation-free events, so the
untruncated count diverges above order `exp((1+ε)pn)` for `Y \ T` too.

## Scope

`t` may grow with `n`. The proof gives the conclusion whenever
`(t+1)! e^t (pn)^t exp(-pn/60) -> 0` and `t <= pn/3`, for instance
`t <= pn/(200 log(pn))`.
