---
rg: 2
id: oracularizable-tracial-nonru-game-exists
kind: claim
title: A finite incidence-oracularizable game has perfect commuting value and a finite-dimensional gap
distinct_from:
  mipstar-bcs-tracial-nonru-exists: that supplies the separated constraint-constraint BCS; this claim applies the symmetrized constraint-variable incidence conversion that makes every sampled pair compatible.
  taller-vidick-lcs-re-hardness: that supplies perfect oracularizable strategies on the halting side and a finite-dimensional gap on the nonhalting side, but not both properties for one input.
---

There is a finite synchronous constraint-variable BCS game `G_cv` with

```text
omega_co(G_cv)=1,
omega_qa(G_cv)<1,                                          (OTN1)
```

and a perfect commuting strategy whose answer measurements are
**oracularizable** on every question pair used by the projection front end:
the two answer PVMs admit a joint PVM with the correct marginals.

Take the Paddock--Slofstra BCS with a tracial state and no `R^U`
representation and apply Fu--Mastel--Zhang's symmetrized
constraint-variable construction.  Its only sampled pairs are the same
constraint, the same variable, or an incident constraint and variable.  In
the tracial BCS algebra these PVMs commute, and a context atom times the wrong
variable outcome is zero.  This gives perfect commuting play and the required
joint measurements.  Fu--Mastel--Zhang soundness transfers the original
quantum-approximable gap to the new game by contrapositive.

## Attempts

- Generic projection of the Paddock--Slofstra game remains invalid: unrelated
  context PVMs need not commute.  The symmetrized constraint-variable
  conversion works because it never samples two unrelated contexts.
- The Dong/Culf--Mastel source used by Taller--Vidick has a perfect
  oracularizable finite-dimensional strategy on YES instances, so its value is
  not separated from one.
- On NO instances the same family has a finite-dimensional gap, but the cited
  theorem does not supply a perfect commuting or oracularizable strategy.

This closes the source interface for the entangled long-code route.  It does
not construct the later multiplicity return.
