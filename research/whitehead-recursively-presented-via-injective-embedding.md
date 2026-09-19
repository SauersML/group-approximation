---
rg: 2
id: whitehead-recursively-presented-via-injective-embedding
kind: route
title: A Whitehead-injective embedding pushes the finitely presented case down
target: whitehead-vanishing-recursively-presented-torsion-free
requires: [whitehead-vanishing-finitely-presented-torsion-free, whitehead-injective-torsion-free-embedding]
artifacts:
  - research/artifacts/whitehead-vanishing-audit-2026-08-17.md
---

Let K be finitely generated, recursively presented, and torsion-free. By the
now-established second requirement there is an embedding K->H with H
finitely presented and torsion-free such that Wh(K)->Wh(H) is injective. The
first requirement gives Wh(H)=0. An injection into the zero group has zero
source, so Wh(K)=0. QED

## Status update

This route used to die at Whitehead injectivity. That gap closed on
2026-08-30 by the Waldhausen--Higman rope construction recorded in
[[whitehead-injective-via-waldhausen-higman-rope]]. Consequently the only
open requirement of this route is now
[[whitehead-vanishing-finitely-presented-torsion-free]] itself. Composed with
[[whitehead-global-via-recursively-presented-reduction]], it makes the
finitely presented, recursively presented, and global vanishing statements
equivalent.
