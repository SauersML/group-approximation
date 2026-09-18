---
rg: 2
id: kazhdan-subgroups-of-almost-v-have-no-central-v-elements
kind: claim
title: A Kazhdan group of homeomorphisms of the Cantor set with finite V-singular sets has no central element of infinite order lying in a conjugate of V
distinct_from:
  thompson-v-has-haagerup-property: that says every Kazhdan subgroup of V is finite; this says a Kazhdan group outside V, with only finitely many singular points per element, still cannot have an infinite-order element of V in its center.
  almost-v-fw-subgroups-act-through-finitely-many-germs: that reduces an FW subgroup of H to finitely many germ groups, with kernel inside a conjugate of V; this shows that kernel can contain no infinite-order central element, which is what the reduction needs for Kazhdan inputs with infinite center.
  type-a-actors-have-no-infinite-virtually-central-subgroup: that forbids infinite virtually central subgroups in type (A) actors; this is a different, dynamical restriction on where an infinite center can sit inside almost-V hosts.
---

**ESTABLISHED** by `kazhdan-almost-v-central-v-elements-proof` (referee-a PASS, research/artifacts/gq-referee-a-kazhdan-almost-v-central-and-normal-germ-extensions.md, bdc9e959c; lane proof, elementary
from landed nodes plus the revealing-pair structure of elements of `V`; citation review by referee-b pending; no novelty claimed).

## Setting

`C = {0,1}^N`, `V <= Homeo(C)` is Thompson's group, and
`H = {g in Homeo(C) : sing(g) is finite}` as in
`almost-v-fw-subgroups-act-through-finitely-many-germs` (points where `g` is not V-local).
Every finite germ extension of `V` in the sense of Belk--Hyde--Matucci, every shell
envelope `E_nu`, and `VA` lie in `H`.

## Statement

Let `Λ <= H` have property (T).

1. **Centralized elements of V.** Let `w in V` have infinite order and commute with every
   element of `Λ`. For every attracting periodic point `a` of `w`, some finite-index
   subgroup of `Λ` fixes the `w`-basin of `a` pointwise.
2. **Central elements.** If `w in Λ` is central and `w in kVk^-1` for some `k in H`, then
   `w` has finite order.

So in a Kazhdan subgroup of any finite germ extension of `V`, every central element of
infinite order is genuinely singular: no conjugate of it by an element of `H` lies in `V`.

## Why it matters

For the Deligne lattice `Gamma~` (`deligne-lattice-satisfies-boone-higman`), the kernel of
the FW germ map is central, and item 2 kills it. That gives
`deligne-lattice-in-almost-v-sits-in-one-germ-group`.

## Scope

- Only property (T) of `Λ` is used, through three standard facts: finite-index subgroups of
  (T) groups have (T), quotients of (T) groups have (T), and (T) groups have finite
  abelianization. Together with `V` Haagerup
  (`thompson-v-has-haagerup-property`).
- `w` must lie in a conjugate of `V`. Central elements of `Λ` that lie in `H` but in no
  conjugate of `V` are not covered.
