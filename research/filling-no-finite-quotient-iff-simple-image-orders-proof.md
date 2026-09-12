---
rg: 2
id: filling-no-finite-quotient-iff-simple-image-orders-proof
kind: route
title: Pass a finite quotient of the filling to a simple quotient, and back
target: filling-no-finite-quotient-iff-simple-image-orders
requires: []
---

Write `Q = Γ/<<g^n>>` and `π: Γ ->> Q`.

**(⇒)** Let `φ: Γ ->> S` be simple with `ord φ(g) | n`. Then `φ(g^n) = 1`, so
`<<g^n>> <= ker φ`, and `φ` factors through `Q`. This gives the nontrivial
finite quotient `Q ->> S`.

**(⇐)** Let `Q ->> F` with `1 != F` finite. Choose a maximal normal subgroup `L`
of `F`; then `S = F/L` is finite simple. Compose `φ: Γ ->> Q ->> F ->> S`.
Since `φ(g)^n = φ(g^n) = 1`, the order of `φ(g)` divides `n`.

**Conditions (1)-(3).**
- (1) is the case `ord = 1`, which divides every `n`.
- For (2), a proper subgroup of the finite abelian group `Γ^ab` lies in a
  maximal subgroup of prime index `p`. That gives `φ: Γ ->> Z/p` with
  `φ(g) = 1` when `g` fails to generate. Otherwise `φ(g)` has order `p`, which
  divides `n` whenever `p | n`.
- (3) is the special case `S = G(O/𝔭)/Z`.

`QED`
