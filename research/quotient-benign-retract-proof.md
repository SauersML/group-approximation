---
rg: 2
id: quotient-benign-retract-proof
kind: route
title: Kill the cutting subgroup and exhibit the quotient as a retract
target: quotient-benign-witness-forces-finite-presentation
requires: []
artifacts:
  - research/artifacts/quotient-benign-rope-synchronization-2026-08-25.md
---

Let `pi:K->P=K/normalClosure(L)`.  Since `L` is finitely generated and `K`
is finitely presented, `P` is finitely presented.  The rule
`i(q(f))=pi(e(f))` is well-defined because `e(N)<=L`.  It is injective:
if `pi(e(f))=1`, then `e(f)` lies in `normalClosure(L)<=ker(sigma)`, hence
`q(f)=sigma(e(f))=1`.

Because `L<=ker(sigma)`, the map `sigma` factors as `r:P->Q`, and
`r i(q(f))=q(f)`.  Thus `r i=id_Q`.  Retracts of finitely presented groups
are finitely presented (equivalently, present the image of the idempotent
`i r` by adjoining one relation `x=(i r)(x)` for each generator of `P`).
The positive FIN/INF limit is not finitely presented by the finite-stage
compactness argument, so its requested witness cannot exist.
