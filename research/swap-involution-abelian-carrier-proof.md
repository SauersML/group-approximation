---
rg: 2
id: swap-involution-abelian-carrier-proof
kind: route
title: Evaluate the four-letter alternating word and expand the commutator square of two involutions
target: swap-involution-enemy-is-never-abelian-carried
requires: []
---

Fix `a in A - C` and write `u = pi(a)`, `s_a = u s u^*`.

**The four-letter moment.**  The word

```text
w = s u s u^* s u s u^*
```

is alternating for the pair `(W*(pi(A)), W*(B, s))` over `B`: the letters
`s` are `E_B`-centered by hypothesis, and the letters `u, u^*` are
`E_B`-centered because `a, a^(-1) in A - C` and `E_B(pi(g)) = 0` for
`g notin C` (regular character; `E_B` is the trace-preserving conditional
expectation onto the subgroup subalgebra).  Amalgamated freeness gives
`E_B(w) = 0`, hence `tau(w) = 0`.  But `w = (s s_a)^2`, proving the first
half of `(AC1)`.

(For letters `u = pi(a)` the centering is exact, so no correction terms
appear; this is the same evaluation that makes the fold mark of
`arithmetic-double-swap-extension-is-binary-coset-wreath` traceless, one
word longer.)

**The commutator norm.**  For self-adjoint unitaries `s, t`:

```text
(st - ts)(st - ts)^* = (st - ts)(ts - st)
  = s t^2 s - (st)^2 - (ts)^2 + t s^2 t
  = 2 - (st)^2 - (ts)^2,
```

so `|| [s, t] ||_2^2 = 2 - 2 Re tau((st)^2)`.  With `t = s_a` and
`tau((s s_a)^2) = 0` this is `2`, the maximum possible value.  If instead
`[s, s_a] = 0` -- as holds for any `s` in an abelian algebra containing
its `a`-twist, in particular for `s = f(x)` in the core of a crossed
product with `s_a = f(a^(-1) x)` -- then `(s s_a)^2 = s^2 s_a^2 = 1` and
`tau((s s_a)^2) = 1`.  The two moment patterns sit at opposite ends of
the interval `[0, 2]` for the commutator square, which proves the
corollary: no abelian-carried involution satisfies the enemy pattern,
with a defect of the full size `2` rather than a perturbative one.
