---
rg: 2
id: mipstar-bcs-tracial-nonru-exists
kind: claim
title: MIP*=RE supplies a finite BCS with a tracial model but no RU model
artifacts:
  - research/artifacts/lcs-exact-support-sparsification-2026-08-18.md
---

Paddock--Slofstra Example 4.2 records the consequence of `MIP*=RE` needed by
this programme: there is a finite Boolean constraint system `B` whose
synchronous algebra has a tracial state but no homomorphism to `R^U`.
Equivalently, `B` is tracially satisfiable but not `R^U`-satisfiable; its game
has a perfect commuting-operator strategy but no perfect quantum-approximable
strategy.

This is **not** yet a nonhyperlinear group.  Paddock--Slofstra Proposition 5.8
shows that obtaining the same separation for the linear constraint language
would be exactly equivalent to a finitely presented nonhyperlinear group.
Thus the source BCS exists unconditionally; the remaining work is a
tracial/approximate-sound groupification into LIN/LCS syntax.
