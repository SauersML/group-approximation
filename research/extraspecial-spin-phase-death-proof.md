---
rg: 2
id: extraspecial-spin-phase-death-proof
kind: route
title: Use the nondegenerate extraspecial commutator pairing
target: extraspecial-spin-predicate-centralization-kills-phase
requires: []
---

The commutator form on `E/<J>` is nondegenerate, so every noncentral `p`
has `x` with `[p,x]=J`.  In a toric clause `beta p b`, the scalar phase and
the other player's word commute with `x`; imposing normal centrality of the
clause therefore gives

```text
1=[beta p b,x]=[p,x]=J.
```

Conjugating `p` by a private letter merely conjugates its witness and leaves
the same central commutator, so it cannot repair the phase.  Conversely the
balanced presentation `<E,t|[t,p]=J>` maps to the finite group `E` by sending
`t` to a commutator witness (choosing orientation if necessary), proving the
claimed finite-model side of the dichotomy.
