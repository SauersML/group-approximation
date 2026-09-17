---
rg: 2
id: finite-field-upper-triangular-cloning-not-in-v-via-lamplighter
kind: route
title: "C_p ≀ Z^2 lies in T(B_*(F_q)), so a non-embedding of C_p ≀ Z^2 in V gives T(B_*(F_q)) not in V"
target: finite-field-upper-triangular-cloning-groups-do-not-embed-in-v
requires:
  - upper-triangular-cloning-groups-contain-lamp-wreath-z2
  - cyclic-p-wreath-z2-does-not-embed-in-thompson-v
---

Let `q = p^e`.

1. By `upper-triangular-cloning-groups-contain-lamp-wreath-z2` with `R = F_q`, the group
   `(F_q,+) ≀ Z^2` is a subgroup of `T(B_*(F_q))`.
2. The prime field `F_p · 1 ≅ C_p` is a subgroup of `(F_q,+)`. Its lamps `λ ∈ F_p · 1` span a copy
   of `C_p ≀ Z^2`.
3. Suppose `ι: T(B_*(F_q)) → V` is injective. Then `ι` restricts to an embedding of `C_p ≀ Z^2`
   in `V`, which contradicts `cyclic-p-wreath-z2-does-not-embed-in-thompson-v`. ∎

**Status.** The route is complete once its second prerequisite is established. The first
prerequisite is ESTABLISHED (unreviewed).

**What could fail.** The second prerequisite could be false. If `C_p ≀ Z^2` does embed in `V`, this
route dies, and `T(B_*(F_q))` stays a candidate for the embedding half of Problem 2.16.
