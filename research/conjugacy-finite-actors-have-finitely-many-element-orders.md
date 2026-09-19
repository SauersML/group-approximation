---
rg: 2
id: conjugacy-finite-actors-have-finitely-many-element-orders
kind: claim
title: "Two-sided translation actors Γ × Γ of conjugacy-finite groups, and the translation part S of orbit-finite affine actors, have finitely many element orders, so they never contain an input with infinitely many element orders"
distinct_from:
  every-wp-group-embeds-in-fp-conjugacy-finite-group: that is refuted for finitely presented envelopes by the same order count applied to V; this records the count for FP_2 two-sided actors Γ × Γ and for the translation subgroup of affine actors, and states which inputs of Problem 1.25 it excludes.
  bvc-groups-have-bounded-finite-subgroups: that bounds finite subgroups under property BVC; this bounds element orders under finitely many conjugacy classes, a purely combinatorial count.
---

**ESTABLISHED** by `conjugacy-finite-actors-have-finitely-many-element-orders-proof`.
Elementary.

1. If `Γ` has `k` conjugacy classes, the elements of `Γ` have at most `k` distinct
   orders (in `N ∪ {∞}`), and the elements of `Γ × Γ` have at most `k^2`.
2. If `W ≤ Aut(S)` has `k` orbits on `S`, the elements of `S` have at most `k`
   distinct orders.
3. **Class-kill for Problem 1.25.** No group with infinitely many element orders
   (for example `Q/Z`, `⊕_n Z/n`, Thompson's `V`, or any group containing all
   finite groups) embeds in `Γ × Γ` with `Γ` conjugacy-finite. So case (B) of
   `orbit-finite-fp2-affine-actors-are-faithful-ha2-actors` cannot prove
   `every-countable-group-lies-in-a-faithful-ha2-actor`, whatever finiteness is
   assumed of `Γ`. Such inputs can lie in an affine actor `S ⋊ W` only with
   infinitely many orders coming from outside `S`: an input `G` meets `S` in a
   subgroup of bounded orders and `G/(G ∩ S)` embeds in `W`.
4. For torsion-free inputs, and inputs with finitely many element orders, the
   count gives no obstruction.
