---
rg: 2
id: oracularizable-tracial-nonru-game-exists
kind: claim
title: Find a finite oracularizable game with perfect commuting value and a finite-dimensional gap
distinct_from:
  mipstar-bcs-tracial-nonru-exists: that supplies a finite BCS with perfect commuting play and no perfect quantum-approximable play, but its context measurements are not known to admit the joint answers required by projection-game oracularization.
  taller-vidick-lcs-re-hardness: that supplies perfect oracularizable strategies on the halting side and a finite-dimensional gap on the nonhalting side, but not both properties for one input.
---

Construct one finite game `G` with

```text
omega_co(G)=1,
omega_qa(G)<1,                                               (OTN1)
```

and a perfect commuting strategy whose answer measurements are
**oracularizable** on every question pair used by the projection front end:
the two answer PVMs admit a joint PVM with the correct marginals.

This extra clause is not implied by perfect commuting play.  In a BCS tracial
model, observables commute within each context, while PVMs belonging to two
different contexts need not commute.  Asking Alice to answer both questions in
a projected game therefore requires new compatibility.

## Attempts

- Paddock--Slofstra Example 4.2 gives `(OTN1)` without oracularizability.
- The Dong/Culf--Mastel source used by Taller--Vidick has a perfect
  oracularizable finite-dimensional strategy on YES instances, so its value is
  not separated from one.
- On NO instances the same family has a finite-dimensional gap, but the cited
  theorem does not supply a perfect commuting or oracularizable strategy.
- Generic projection of the Paddock--Slofstra BCS is invalid: a joint answer to
  two contexts would impose cross-context commutation absent from its algebra.

A positive solution would feed the entangled long-code test with both exact
tracial completeness and finite soundness.  It is a source-interface theorem,
not the later multiplicity return.
