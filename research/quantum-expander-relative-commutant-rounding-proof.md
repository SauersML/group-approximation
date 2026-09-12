---
rg: 2
id: quantum-expander-relative-commutant-rounding-proof
kind: route
title: Invert one minus the expander channel off its fixed algebra
target: quantum-expander-relative-commutant-rounding
requires: []
---

On the Hilbert space `L^2(M_N) tensor L^2(M_r)`, the fixed space of
`Phi tensor id` is `I_N tensor M_r`, and its orthogonal projection is `E`.
Tensoring with the identity preserves the operator-norm bound `lambda` on the
orthogonal complement. Thus, for `Y=X-E(X)`,

```text
(1-lambda)||Y||_2 <= ||Y-(Phi tensor id)(Y)||_2
                    = ||X-(Phi tensor id)(X)||_2.                (QEC2)
```

The last term is the average of

```text
X-(U_j tensor I)X(U_j* tensor I)
 = [X,U_j tensor I](U_j* tensor I).
```

Triangle inequality and then Cauchy--Schwarz over `j` bound `(QEC2)` by the
right side of `(QEC1)` multiplied by `1-lambda`. Division proves the claim.
