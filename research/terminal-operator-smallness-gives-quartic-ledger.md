---
rg: 2
id: terminal-operator-smallness-gives-quartic-ledger
kind: claim
title: Operator-small terminal off-diagonals give the missing quartic balanced ledger
distinct_from:
  aggregate-terminal-even-defect-is-quartic-summable: that asks the adaptive cut tree itself to manufacture a small coefficient; this proves the analytic ledger once final aggregate operator-smallness is supplied.
  common-cut-contraction-sign-has-complete-balanced-energy-ledger: that is unconditional and therefore pays linearly in terminal displacement; this gains a factor from an operator bound on every final off-diagonal generator.
---

ESTABLISHED.  Let `Phi` be a common finite pinching, let `B_1,...,B_L`
be reflections, and put

```text
X_i=Phi(B_i),   O_i=B_i-X_i,
D=L^(-1)sum_i||O_i||_2^2,
theta=max_i||O_i||_op^2.                              (OSQ1)
```

For the positive square function `A=L^(-1)sum_i O_i^2`,

```text
L^(-2)sum_(i,j)||[O_i,O_j]||_2^2
 <=4 tau(A^2)<=4||A||_op D<=4 theta D.                (OSQ2)
```

Every fixed-width parity compression remainder is bounded by
`C_m theta` times the sum of the squared boundary norms of the generators
occurring in that word.  Moreover terminal sign repair obeys

```text
||sgn(X_i)-X_i||_2^2
 <=tau(O_i^4)<=theta||O_i||_2^2.                       (OSQ3)
```

Consequently, for any bounded-width, bounded-occurrence balanced code with
the normalized complete-pair layer, the terminal signed tuple satisfies

```text
E_bal(sign(Phi(B)))<=C(E_bal(B)+theta D),              (OSQ4)
```

where `C` depends only on the fixed face width and occurrence bounds.  In
particular `theta=o(1)` gives exactly the nonlinear coefficient sought by
the aggregate quartic terminal ledger.

The weaker bound `||A||_op<=theta` alone proves the complete-pair part of
`(OSQ4)`, but does not by itself control individual parity words or the
diagonal fourth moments in `(OSQ3)` without an additional row-Carleson
estimate.
