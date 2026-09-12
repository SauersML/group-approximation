---
rg: 2
id: atlas-low-rank-cyclic-promotion-proof
kind: route
title: Telescope each Laurent word across the low-rank gauge perturbation
target: atlas-low-rank-cyclic-perturbations-promote
requires:
  - atlas-block-circulant-joint-escape-promotes-to-exact-mode
---

For invertible matrices `S,T`,

```text
T^-1-S^-1=T^-1(S-T)S^-1,
rank(T^-1-S^-1)=rank(T-S).                             (LCP2)
```

Let `w` be any one of the finitely many augmented Atlas Laurent words, and
let `ell_T(w)` count its occurrences of `T` or `T^-1`.  Telescoping the two
evaluations one letter at a time, while multiplying on the left and right by
invertible coefficient/word matrices, gives

```text
rank(w(T)-w(S)) <= ell_T(w) rank(T-S).                 (LCP3)
```

Therefore

```text
rank(w(S)-I)
 <=rank(w(T)-I)+ell_T(w) rank(T-S).                   (LCP4)
```

The relation list and all `ell_T(w)` are fixed independently of `N`, so the
right side is `o(N)` under the hypotheses.  Every augmented residual at the
block-circulant `S_N` is consequently `o(N)`.  The established primary-mode
promotion theorem now supplies a finite-extension exact zero, completing the
proof.

