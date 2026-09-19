---
rg: 2
id: add-a-split-quotient-summand-and-keep-the-diagonal-kernel-word
kind: route
title: Split through the quotient summand while retaining kernel holonomy in the first summand
target: overlap-and-kernel-floors-do-not-exclude-splitting
requires:
  - three-face-ucp-balancing-needs-macroscopic-tree-motion
  - scalar-tree-perturbations-linearly-control-closing-face
---

Both coordinate maps in `(OKF2)` are unital star homomorphisms: augmentation
on the first coordinate and the identity on the second.  Their direct sum is
therefore a unital star homomorphism, and `q_split s_split=id_Q` proves exact
splitting.

Equation `(OKF3)` is also a group homomorphism.  Since `q_0(n)=1`, its value
on the kernel word is `(u_n,1)`.  The first coordinate is the same faithfully
embedded infinite-order kernel unitary used in `(TFB3)`, so `(OKF4)` follows.

Now repeat the proof of `(TFB3)` with codomain `A_split` and canonical letters
`w_j^split`.  It uses only Stinespring positivity, `v_1...v_L=1`, and
`||1-Delta(n)||=2`; all three remain true.  Thus

```text
2<=(L-1)sqrt(2 alpha)+L alpha,
alpha=max_j||Phi(v_j)-w_j^split||,
```

and hence `alpha>=2/L^2`.  Substitution of `(OKF2)` gives `(OKF6)`, showing
directly how the exact section pays rather than violates the Gram floor.

Finally, on every nontrivial face element the second coordinate of `s_split`
is the identity representation, while scalar augmentation has scalar second
coordinate.  Hence the section is not approaching the scalar-tree anchor.
It is simultaneously far from the diagonal canonical lift by `(OKF5)`, so it
lies in the advertised middle region.
