---
rg: 2
id: common-padding-julia-rank-proof
kind: route
title: Pad both vertices by one common exact representation
target: common-padding-erases-julia-derivation-density
requires:
  - julia-derivation-rank-controls-fold
---

On the padding block the two vertex maps in `(CPJ2)` are identical. Hence
every edge relation is exact there, and every word in the kernel of the fold
evaluates to `1_N`. Direct sums take the maximum of operator norms, so the
old edge errors and fold-word gaps are unchanged. For a general word, the
old block remains a direct summand, so its old separation is retained.

For every generator `x`,

```text
[sigma^(N)(x),V^(N)]=[sigma(x),V] directSum 0_N.        (CPP1)
```

Thus every summand in `R_X` has unchanged rank while the total dimension is
`d+N`, proving `(CPJ3)`.

Apply this at coordinate `n` with `N_n/d_n->infinity`. Exact direct-sum
padding preserves asymptotic multiplication and all upper operator-norm
defect bounds. Every nontrivial word which was separated in the original
norm-corona model remains separated by its old block, so the padded model is
still faithful. Equation `(CPP1)` makes its derivation-rank density vanish.

Finally `(CPJ4)` and inequality `(JDG5)` from
`julia-derivation-rank-controls-fold` give a uniform lower bound on
`R_X/d`. This proves both the no-go and the stated boundary of a genuinely
stronger construction.
