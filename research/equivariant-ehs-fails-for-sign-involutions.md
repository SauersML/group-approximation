---
rg: 2
id: equivariant-ehs-fails-for-sign-involutions
kind: claim
title: The equivariant Effros-Handelman-Shen theorem fails, order-two dimension group automorphisms need not come from simplicial involution chains
artifacts:
  - research/artifacts/stw99-lii-equivariant-ehs-obstruction-2026-08-30.md
---

There is a countable dimension group with order unit and an order-two
order-automorphism fixing the unit which is NOT an equivariant
inductive limit of simplicial ordered groups `(Z^{n_k}, standard cone)`
with order-two order-automorphisms at the stages.  Explicit witness:
fix irrational `θ` and take

```text
G = Z^3,   G_+ = {(x,y,z) : x + θy > 0} ∪ {0},   u = (1,0,0),
α = diag(1, 1, −1).
```

`(G, G_+)` is a dimension group with infinitesimal subgroup the third
axis, `α` is a cone-preserving involution fixing `u`, and
`H^1(Z/2, G) = Z/2 ≠ 0`, while every equivariant simplicial chain has
`H^1(Z/2, ·) = 0` in the limit.

Consequence for STW Problem LII
(`stw99-problem-lii-lift-actions-on-invariant`) and Blackadar's
lifting question: IF an order-two automorphism `β` of the AF algebra
`A_G` induces `α` on `K_0`, then `β` preserves NO exhausting nest of
finite-dimensional subalgebras — it is necessarily exotic in the sense
of Blackadar's CAR symmetry.  The "equivariant EHS" strategy recorded
as the natural attack on the simple-AF case of LII is therefore dead
in general, and `(G, α)` is the minimal sharp test case for
Blackadar's question itself: either lift `α` exotically, or refute
Blackadar on a rank-three dimension group with one infinitesimal
direction.
