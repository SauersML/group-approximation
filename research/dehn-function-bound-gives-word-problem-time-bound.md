---
rg: 2
id: dehn-function-bound-gives-word-problem-time-bound
kind: claim
title: A recursive upper bound on the Dehn function bounds the word-problem time by a double exponential of it
distinct_from:
  hs-dehn-modulus-bounded-by-dehn-function: that bounds the Hilbert--Schmidt stability modulus of a presentation by its Dehn function; this bounds the running time of a deterministic word-problem algorithm by a function of an upper bound on the Dehn function.
  simple-envelope-forces-solvable-word-problem: that proves decidability of the word problem for subgroups of finitely presented simple groups, with no time bound and no Dehn function; this is a quantitative time bound valid for every finitely presented group.
---

**ESTABLISHED.** Let `S = <X | R>` be a finite presentation with Dehn function
`delta_S`. Let `f: N -> N` be non-decreasing with `f(n) >= n`, computable in time
at most `C_0 f(n)^2`. If `delta_S ≼ f`, then the word problem of `S` over `X` is
decided by a deterministic algorithm running in time at most

```text
2^(C (f(C l) + l)^2) + C                                   (DW1)
```

on words of length `l`, for a constant `C` depending on the presentation, on `C_0`
and on the constant in `delta_S ≼ f`.

Consequence: if the word problem of `S` has no algorithm within `(DW1)` for any
`C`, then `delta_S ⋠ f`. Every recursive function is bounded above by a
non-decreasing recursive `f' >= n` computable in time `C_0 f'(n)^2`, so the
hypotheses on `f` cost nothing in applications
(`fp-simple-unbounded-dehn-via-complex-word-problem`).

**Model test.** For the free group `<a, b | >` the area of every trivial word is
`0`, and `(DW1)` holds with room to spare, since free reduction is linear. For
`BS(1,2)`, which has exponential Dehn function and polynomial-time word problem,
`(DW1)` is a doubly exponential upper bound. It is only an upper bound, which is
why Dehn growth forces nothing about hardness.

DERIVATION
dehn-function-bound-gives-word-problem-time-bound-proof
