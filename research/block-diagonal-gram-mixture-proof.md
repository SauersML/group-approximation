---
rg: 2
id: block-diagonal-gram-mixture-proof
kind: route
title: Compute the exact classical mixture carried by a block diagonal Gram operator
target: block-diagonal-pair-grams-do-not-add-coverage
requires: []
---

Let `G_j` decode a strategy `S_j`, and after common amplification put

```text
G=directSum_j t_j G_j.
```

Normalized vectorization splits orthogonally over the central blocks.  The
probability of block `j` is

```text
lambda_j=t_j^2||G_j||_2^2 / sum_l t_l^2||G_l||_2^2,
```

so direct-sum measurements give the exact identity

```text
value(S_G)=sum_j lambda_j value(S_j).
```

If block `j` is certified only on a verifier set `C_j`, with error
`epsilon_j`, the unconditional bound is

```text
value(S_G)>=sum_j lambda_j(mu(C_j)-epsilon_j)
           <=max_j mu(C_j)+small error.
```

The hidden central label is sampled before, and independently of, the
verifier questions.  Hence the right side cannot be replaced by
`mu(union_j C_j)`.  Rescaling merely concentrates on the best block.

For pair blocks on `k` uniformly weighted contexts, even granting perfect
play on both endpoint context stars gives `mu(C_j)=2/k`.  In the actual
oriented cross-Gram construction only shared-variable incidences are
certified, so the true mass is no larger.  Adding the reverse orientation
is another mixture component, not a two-sided state.  This proves the
claim.
