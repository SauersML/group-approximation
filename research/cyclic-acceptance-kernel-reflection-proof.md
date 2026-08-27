---
rg: 2
id: cyclic-acceptance-kernel-reflection-proof
kind: route
title: Package cyclic acceptance in one root and separate positivity from kernel reflection
target: cyclic-acceptance-root-needs-kernel-reflection
requires: []
---

Write `T_game(G)=sum_s beta_sU_sGV_s` and choose a fixed integer `D` clearing
all coefficients.  Then

```text
C_acc=D(T_game(G)-G),
g_acc=x_12(C_acc)
```

is a single coefficient and a single Steinberg root.  The strict game
contraction gives

```text
||C_acc||_2^2>=D^2 kappa^2||G||_2^2.
```

Thus a theorem saying `g_acc=1` in a canonical matrix ultraproduct implies
`C_acc=0` would immediately kill positive Gram mass.  Positivity proves only
the displayed lower bound and does not imply that theorem.

For separation, tensor any exact finite game table with the regular `D_8`
Pauli packet and set `G=(I+X)/2 tensor I`.  Then `||G||_2^2=1/2` and the game
gap keeps `||C_acc||_2` uniformly positive.  Tensor independently with an
exact finite root packet whose designated coordinate is the identity.  All
game, cyclic-product, root-table, and Plancherel identities are exact, while
the root coordinate has zero word defect and `C_acc` remains nonzero.

This is not a model of a coupled coefficient presentation; precisely for
that reason it proves that an additional mixed kernel-reflection relation is
the necessary interface.  In the exact perfect model `G=I` gives
`C_acc=0`, so adding that interface is compatible with completeness.
