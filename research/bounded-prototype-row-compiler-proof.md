---
rg: 2
id: bounded-prototype-row-compiler-proof
kind: route
title: Telescope finitely many prototype fillings and use conjugacy isometry
target: bounded-prototype-rows-imply-atomic-morita-return
requires:
  - atomic-morita-return-kills-finite-order-mf-mark
  - conjugacy-addressed-opnorm-challenges-are-lossless
---

Each fixed `q_j` has one fixed expression as a product of conjugates of the
finite relators and their inverses.  Telescoping that expression gives a
constant `A_j`, independent of matrix dimension, with

```text
||q_j(U)-1||_op <= A_j Def_R(U).                       (BPP1)
```

Evaluation of every address word is unitary.  Therefore

```text
||(a^-1 q_j a)(U)-1||_op=||q_j(U)-1||_op              (BPP2)
```

regardless of the length of `a`.  Combining `(BPR1)` with `(BPP1)` gives
the AMR modulus

```text
eta(delta)=C (max_j A_j) delta.
```

The coordinate-dependent window and address need not be compatible with
those chosen at any other coordinate.  Apply the atomic return collapse
theorem to obtain the MF-radical conclusions.

