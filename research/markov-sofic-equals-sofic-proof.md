---
rg: 2
id: markov-sofic-equals-sofic-proof
kind: route
title: Approximate inverses round every Markov table to a sofic permutation table
target: markov-sofic-equals-sofic
requires:
  - birkhoff-approx-inverse-permutation
---

Fix a finite table containing `e`, all tested products and inverse pairs. Let
its doubly stochastic model have defect `delta` and `||P_e-I||_2 <= delta`.
Then

```text
||P_g P_{g^{-1}}-I||_2 <= 2 delta.
```

By `birkhoff-approx-inverse-permutation`, choose a permutation `S_g` with
`||P_g-S_g||_2 = O(sqrt(delta))`. For a tested product `gh=k`, insert the
three rounded matrices and use `||P||_op <= 1` for doubly stochastic `P` and
`||S||_op=1` for permutations:

```text
||S_g S_h-S_k||_2
 <= ||S_g-P_g||_2 + ||S_h-P_h||_2
    + ||P_gP_h-P_k||_2 + ||P_k-S_k||_2
 = O(sqrt(delta)).
```

Squaring and using `||S-T||_2^2=2 d_H(S,T)` gives Hamming defect `o(1)`.
Moreover `|tau(S_g)-tau(P_g)| <= ||S_g-P_g||_2`, so regular trace separation
passes to the permutations. Hence Markov-sofic implies sofic. The reverse
implication is obtained by taking the permutation matrices of a sofic model.
