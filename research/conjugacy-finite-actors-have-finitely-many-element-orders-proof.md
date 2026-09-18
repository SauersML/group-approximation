---
rg: 2
id: conjugacy-finite-actors-have-finitely-many-element-orders-proof
kind: route
title: Element order is a conjugacy invariant and an automorphism invariant
target: conjugacy-finite-actors-have-finitely-many-element-orders
requires: []
---

1. Conjugate elements have equal order, so the order function on `Γ` is constant
   on each of the `k` classes and takes at most `k` values. The order of `(a,b)`
   in `Γ × Γ` is `lcm(o(a), o(b))` (infinite if either is infinite), so it is
   determined by the pair `(o(a), o(b))`, which takes at most `k^2` values.
2. An automorphism preserves order, so the order function on `S` is constant on
   each `W`-orbit.
3. If `G ≤ Γ × Γ`, the orders of elements of `G` are among those of `Γ × Γ`,
   finitely many. The listed groups have infinitely many orders: `Q/Z` and
   `⊕_n Z/n` contain elements of every order `n`, and `V` contains every finite
   group, in particular every cyclic group. For `G ≤ S ⋊ W`, `G ∩ S` has orders
   among those of `S` and `G/(G ∩ S) ≅ GS/S ≤ (S ⋊ W)/S ≅ W`.
4. Nothing to prove. `∎`
