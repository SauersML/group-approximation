---
rg: 2
id: abelian-lamp-wreaths-cannot-create-u3-q-or-aff-q
kind: claim
title: In a permutational wreath product with abelian lamps and finite point stabilizers, nonabelian torsion-free nilpotent subgroups and copies of Aff(Q) meet the base trivially and so embed in the top group
distinct_from:
  permutational-boone-higman-closed-under-wreath-products: that is the closure of the permutational class under these wreath products; this shows that with abelian lamps the closure cannot create U_3(Q), H_3(Z) or Aff(Q) that the top group lacks.
  bffhz-closures-cannot-create-gl-n-q: that covers the BFFHZ free-product and mapping-torus closures; this covers permutational wreath products with abelian lamps.
  lifts-add-no-unipotent-divisibility: that covers central and covering lifts; this covers wreath products.
---

**ESTABLISHED** through `abelian-lamp-wreaths-cannot-create-u3-q-or-aff-q-proof`.
Lane-proved, not independently reviewed. The argument is elementary and no
priority is claimed.

## Statement

Let `A` be an abelian group, `G` a group, and `X` a `G`-set whose point
stabilizers are finite. Let `W = A wr_X G = (⊕_X A) ⋊ G` be the restricted
permutational wreath product, with base `B = ⊕_X A` and projection
`π : W -> G`. Let `H <= W`.

1. **Nilpotent case.** If `H` is torsion-free nilpotent and nonabelian, then
   `H ∩ B = 1`, so `π` embeds `H` in `G`.
2. **Affine case.** If `H ≅ Aff(Q) = Q ⋊ Q^x`, then `H ∩ B = 1`, so `π` embeds
   `H` in `G`.

In particular the rational Heisenberg group `U_3(Q)`, every `U_n(Q)` with
`n >= 3`, the integral Heisenberg group `H_3(Z)`, and `Aff(Q)` lie in `W` only
if they already lie in `G`.

## Consequences for the GL_n(Q) swarm

- `permutational-boone-higman-closed-under-wreath-products` (finite point
  stabilizers) with abelian lamps adds nothing for the stepping stones
  `u3-q-embeds-in-fp-simple-group` and `Aff(Q)`: the top group must already
  contain them. Lamps can still carry abelian pieces such as `(Q,+)`.
- `GL_n(Q)` contains `Aff(Q)` for `n >= 2` and `U_3(Q)` for `n >= 3`. Each such
  copy inside `W` maps injectively to `G`.
- **Remark, not part of the established statement.** Combined with the classical
  fact that an abelian normal subgroup of `GL_n(F)`, `n >= 2`, `F` a field with
  more than three elements, consists of scalars, Lemma 1 of the proof shows that
  `GL_n(Q)` meets `B` trivially. That fact is not quoted from a source here.

## What the proof uses

Only that an element of `G` of infinite order acts freely on `X` (finite
stabilizers), so the base is a free `Z[t^{±1}]`-module over it, together with
uniqueness of roots in torsion-free nilpotent groups (proved in the route).
