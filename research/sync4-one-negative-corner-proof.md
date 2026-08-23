---
rg: 2
id: sync4-one-negative-corner-proof
kind: route
title: Resolve the four one-negative characters in the rational C2-four corner
target: sync4-one-negative-abelian-corner-wordizes-arbitrary-pvm
requires: []
---

## Direct proof

Let `K=(C_2)^4=<r_0,r_1,r_2,r_3>`.  Because every character of `K` is
`Q`-valued, its primitive central idempotent is

```text
p_epsilon=(1/16) product_a (1+epsilon_a r_a).
```

The sixteen `p_epsilon` are pairwise orthogonal, sum to `1`, and satisfy
`r_a p_epsilon=epsilon_a p_epsilon`.  Let `p_b` be the character which is
negative exactly in coordinate `b`, and put `q=sum_b p_b`.  Then `q` is a
central rational projection.  The canonical group trace of every
`p_epsilon` is its identity coefficient `1/16`, so `tr(q)=4/16=1/4`.
Since `Q[K]` is the direct sum of its sixteen rational character lines,
compression gives

```text
q Q[K] q = directSum_(b=0)^3 Q p_b.
```

On the `p_b` summand, `r_a` acts by `-1` when `a=b` and by `+1`
otherwise.  Hence

```text
r_a q = sum_(b!=a) p_b - p_a = q-2p_a.
```

Now let `(E_0,E_1,E_2,E_3)` be any four-outcome PVM.  The assignment
`p_a -> E_a` extends uniquely to a unital star representation of the
corner because the `p_a` are four orthogonal minimal central projections
summing to `q`; under this representation `r_a q` maps to `1-2E_a`.
There is no condition on the individual ranks or traces of the `E_a`.
Conversely, any unital star representation of the corner sends the four
`p_a` to pairwise orthogonal projections summing to `1`, hence to a
four-outcome PVM, and the same identity recovers each atom reflection as
the literal group element `r_a` compressed by `q`.
