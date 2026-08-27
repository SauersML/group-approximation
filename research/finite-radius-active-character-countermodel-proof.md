---
rg: 2
id: finite-radius-active-character-countermodel-proof
kind: route
title: Extend each partial actor map independently and use the regular character PVM
target: finite-radius-active-character-packets-do-not-collapse-the-mark
requires: []
---

Every isomorphism between two equal-dimensional subspaces of a finite vector
space extends to an automorphism of the whole vector space: extend a basis
of the source and its image basis to bases of `W`.  For each `a`, choose such
an extension `T_a` independently.

On `H=ell^2(W_hat)`, let

```text
rho(w) delta_chi = chi(w) delta_chi.
```

This is the regular representation of the additive group `W`; hence every
nonidentity `rho(w)` has normalized trace zero.  Let `U_a` permute the basis
by the contragredient action of `T_a`.  Direct substitution gives

```text
U_a rho(v) U_a^*=rho(T_a v),
```

which is `(FRC2)` on `V_a`.  For a nonzero active root the trace-zero
identity gives `(FRC3)`.

If all independently chosen extensions also obeyed every actor relator and
mixed loop relation, their action would make the finite PVM support an exact
finite actor set.  The aperiodicity theorem rules that out on a surviving
active character.  Therefore some such loop, necessarily absent from the
local partial-map hypotheses, is where the exact model fails.
