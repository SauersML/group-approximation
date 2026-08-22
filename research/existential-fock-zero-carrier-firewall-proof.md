---
rg: 2
id: existential-fock-zero-carrier-firewall-proof
kind: route
title: Apply finite trace to the common source and isolate the zero witness
target: existential-fock-library-has-zero-carrier-or-regular-firewall
requires:
  - universal-block-return-violates-the-regular-firewall
  - bespoke-extension-nemesis-library-defeats-diagonal-schedules
---

In a finite tracial von Neumann algebra, `(EFL1)` gives

```text
tau(v_i v_i^*)=tau(v_i^*v_i)=tau(p).
```

Orthogonality of the ranges therefore gives `(EFL2)`.  Conjugate no-return
projections have the same trace, so their sum gives the identical bound.
Apply this in the left regular finite factor of the final group.  If the same
nonzero algebraic `p` supports the gadgets for unbounded `M`, faithfulness of
the canonical trace gives the contradiction.

If `p` is instead an auxiliary corner whose full gadget admits the stipulated
collapsed assignment over every base representation, choose that assignment;
all source, range and orthogonality equations vanish, so the literal Fock
part excludes no extension type.
For distinct `p_M`, the same trace calculation gives
`tau(p_M)<=1/M` separately but no contradiction.  Returning their vanishing
masses to a fixed mark is an additional coverage statement, not part of the
Fock relations.  This proves the dichotomy.
