---
rg: 2
id: finite-subgroups-of-full-cantor-groups-conjugacy-criterion
kind: claim
title: In a full clopen-transitive group of Cantor homeomorphisms, two finite subgroups with clopen fixed sets are conjugate along an isomorphism exactly when their stabilizer types agree; free finite subgroups are always conjugate, and extend to every finite overgroup
distinct_from:
  fp-clopen-transitive-full-cantor-groups-have-type-a-actions: that gives such groups a type (A) action on proper clopens; this is a conjugacy criterion for their finite subgroups, used to realize finite-edge amalgams and HNN extensions.
  free-permutational-products-preserve-pbh: that realizes amalgams and HNN extensions over finite subgroups once a conjugating overgroup exists; this supplies the conjugating element inside full Cantor hosts.
---

**ESTABLISHED** by `finite-subgroups-of-full-cantor-groups-conjugacy-criterion-proof`
(lane proof, elementary, not reviewed; no priority claimed; the free case for Thompson's
`V` is presumably folklore).

## Setting

Let `Y` be a Cantor space and `D ≤ Homeo(Y)`. As in
`fp-clopen-transitive-full-cantor-groups-have-type-a-actions`:
- a *D-local map* is a homeomorphism `f: U -> U'` between clopen sets that agrees near
  every point with an element of `D`;
- `D` is **full** if every D-local homeomorphism of `Y` lies in `D`;
- `D` is **clopen transitive** if any two nonempty clopen sets are joined by a D-local map.

`D` need not be finitely presented here.

For a finite subgroup `H ≤ D` and `K ≤ H`, write `Y_K(H) = {y : Stab_H(y) = K}`. Say `H`
has **clopen fixed sets** if `Fix(h)` is clopen for every `h ∈ H`. Then every `Y_K(H)` is
clopen. Its **type set** is `Σ(H) = {K ≤ H : Y_K(H) ≠ ∅}`.

## Statement

Let `D` be full and clopen transitive, `H_1, H_2 ≤ D` finite with clopen fixed sets, and
`θ: H_1 -> H_2` an isomorphism.

1. **Criterion.** There is `β ∈ D` with `β h β^(-1) = θ(h)` for all `h ∈ H_1` iff
   `θ(Σ(H_1)) = Σ(H_2)`.
2. **Free case.** If `H_1` and `H_2` act freely on `Y`, such a `β` exists. Free actions
   have `Σ = {1}` and empty fixed sets.
3. **Finite overgroups.** If `F ≤ D` is finite and acts freely, and `E` is a finite group
   containing `F`, then some embedding `E -> D` restricts to the inclusion on `F`.

## Examples

- **`D = V`.** Thompson's `V` is full and clopen transitive. Every finite-order element of
  `V` permutes the cones of some partition by prefix replacement, so its fixed set is
  clopen. So part 1 is a conjugacy criterion for finite subgroups of `V`.
  - Two involutions of `V`, one free and one with a fixed cone, are **not** conjugate in
    `V`. Their type sets are `{1}` and `{1, Z/2}`.
- **`T ≤ V`.** Every nontrivial finite-order element of Thompson's `T` acts on the circle
  without fixed points. An orientation-preserving circle homeomorphism of finite order with
  a fixed point is the identity. The quotient map from the Cantor set to the circle is
  `T`-equivariant, so every finite subgroup of `T` acts freely on the Cantor set.
  - So any two isomorphic finite subgroups of `T` are conjugate in `V` along any
    isomorphism.
  - Example: an element `r ∈ T` of order 3 is conjugate to `r^2` in `V`. They are not
    conjugate in `T`, or even in `Homeo+(S^1)`, because their rotation numbers are `1/3`
    and `2/3` in some order.

## Lesson for general BH

Fullness turns local data into global conjugacy. In a full clopen-transitive host, a
partial isomorphism between subgroups is realized by an element of the host as soon as
the two actions are conjugate by a *D-local* map, which can be glued from pieces. For
finite subgroups the only obstruction is the stabilizer-type set. So combination
theorems for `B_A` (amalgams and HNN extensions) reduce to matching local invariants
inside one full host, not to building new actors. The finite-edge application is
`finite-edge-graphs-of-full-cantor-subgroups-lie-in-b-a`.
