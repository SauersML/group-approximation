---
rg: 2
id: gl-n-f2t-bh-via-leavitt-field
kind: route
title: A copy of F_2(t) inside the binary Leavitt algebra puts every GL_n(F_2(t)) in its finitely presented simple unit group
target: gl-n-f2t-embeds-in-fp-simple-group
requires:
  - rational-function-field-embeds-in-binary-leavitt-algebra
  - leavitt-subalgebra-linear-groups-satisfy-boone-higman
---

Let `R = L_(F_2)(1,2)`, and let `A <= R` be a unital subring isomorphic to `F_2(t)`
(`rational-function-field-embeds-in-binary-leavitt-algebra`). `A` contains the
prime field `F_2`, so it is a unital `F_2`-subalgebra.

By `leavitt-subalgebra-linear-groups-satisfy-boone-higman`, `GL_n(A)` embeds in
`R^x` for every `n >= 1`, and `R^x` is finitely presented and simple (the
finite presentation is an import). Since `GL_n(F_2(t)) ≅ GL_n(A)`, every
`GL_n(F_2(t))` embeds in the single finitely presented simple group `R^x`. `∎`

The route inherits the conditional status of its second input.
