---
rg: 2
id: atlas-word-19243-kernel-proof
kind: route
title: Multiply collision 19243 in the binary Leavitt prefix algebra
target: atlas-word-19243-is-kernel-relation
requires: []
artifacts:
  - experiments/atlas-word-19243.json
  - experiments/atlas_word_19243_trace.py
---

Put `x=t01`, `y=t10`, and `q=t23` in `GL_4(F_2)`.  The stored word is

```text
(yx)_2 q_1 y_2 q_1 (xy)_2 q_1 x_2 q_1.
```

For a binary chart matrix `g`, expand its Leavitt image as the finite
`F_2`-sum of prefix partial isometries `alpha beta^*` selected by the nonzero
matrix entries.  Multiply monomials using only the exact prefix cancellation
rule

```text
(alpha beta^*)(gamma delta^*)
 = alpha epsilon delta^*       if gamma=beta epsilon,
 = alpha (delta epsilon)^*     if beta=gamma epsilon,
 =0                            otherwise.
```

Addition is symmetric difference of the finite monomial supports.  The replay
multiplies the eight displayed factors, expands every final monomial to one
common right-prefix depth using `1=ee^*+ff^*`, and obtains exactly the identity
support.  Its terminal assertion is `final_is_one=true`.  Hence the stored
collision word evaluates to one under the two-chart Leavitt map, proving it is
in the kernel.  Every operation is finite word cancellation over `F_2`; no
trace approximation or numerical tolerance is used.