---
rg: 2
id: baumslag-solitar-chains-of-every-length-lie-in-b-a
kind: claim
title: Every finite Baumslag--Solitar chain T_n = <x_1, ..., x_n | x_i^-1 x_(i+1) x_i = x_(i+1)^2> lies in B_A, with its top cyclic subgroup realized as a centralizer; realization propagates up the tower through preimages under the twisted-lamplighter quotient
requires:
  - higman-chain-group-lies-in-b-a
  - bs12-base-generator-is-a-centralizer-in-b-a
  - pbh-coset-wreaths-iff-identity-edge-hnns
  - type-a-action-gives-boone-higman-for-subgroups
distinct_from:
  higman-chain-group-lies-in-b-a: that is the case n = 3 and gives the general amalgam form; this adds the realization of the new top generator, which is what makes the step repeatable.
  bs12-base-generator-is-a-centralizer-in-b-a: that is the case n = 2; this is the induction it starts.
  baumslag-gersten-group-satisfies-boone-higman: BG is the bi-infinite chain extended by its shift; this handles every finite piece of that chain, but not the shift.
---

**ESTABLISHED** (lane proof, elementary; not reviewed; no priority claimed). It inherits the status of
`higman-chain-group-lies-in-b-a` and its lane chain.

A subgroup `D ≤ G` is **realized** if some `L ∈ B_A` contains `G` and an element `m` with `C_G(m) = D`.
This is condition (e) of `pbh-coset-wreaths-iff-identity-edge-hnns`. Realized subgroups are closed under
finite intersections (item 5 there), and every centralizer `C_G(g)` is realized once `G ∈ B_A`.

## Statement

Let `T_n = ⟨x_1, …, x_n | x_i^-1 x_(i+1) x_i = x_(i+1)^2 (1 <= i < n)⟩`. So `T_2 = BS(1,2)`, and `T_3` is
the chain group `G_1` (`x_1 = a`, `x_2 = b`, `x_3 = c`). For every `n >= 2`:
- **(B_n)** `T_n ∈ B_A`. So `T_n` embeds in a finitely presented simple group.
- **(R_n)** `⟨x_n⟩` is realized in `T_n`.

## Proof

Induction on `n`. The case `n = 2` is `bs12-base-generator-is-a-centralizer-in-b-a`, item 1. Assume
`(B_(n-1))` and `(R_(n-1))`. Write `G = T_(n-1)`, `C = ⟨x_(n-1)⟩`, and `Y = ⟨x_(n-1), x_n⟩ = N_0 ⋊ C`,
with `N_0 = Z[1/2]` the normal closure of `x_n` in `Y ≅ BS(1,2)`. Then `T_n = G *_C Y`.

- **(B_n).** This is item 4 of `higman-chain-group-lies-in-b-a` with `A = G` and `S = {x_(n-1)}`, since
  `C_Y(x_(n-1)) = C`.
- **The quotient map.** Let `N` be the normal closure of `x_n` in `T_n`, and put
  `φ : T_n -> T_n/[N, N]`.
  - As in `higman-chain-configuration-reduction-proof`, `N = *_(G/C) g N_0 g^-1`.
  - So `T_n/[N, N]` is the twisted coset lamplighter `(⊕_(G/C) N_0) ⋊ G`.
  - By item 1 of `higman-chain-group-lies-in-b-a`, it embeds in `Y wr_(G/C) G`, with `N_0` embedded as
    the lamps at the coset `C`.
- **A lamp realizing `⟨x_n⟩` inside `N_0`.** `Y ≅ BS(1,2)` with base generator `x_n`. By item 1 of
  `bs12-base-generator-is-a-centralizer-in-b-a` there are `L_1 ∈ B_A` containing `Y` and `m_1 ∈ L_1` with
  `C_Y(m_1) = ⟨x_n⟩`.
  - `L = L_1 wr_(G/C) G` lies in `B_A`, by `(R_(n-1))` and (e) ⟹ (b).
  - `Y wr_(G/C) G ≤ L`. Let `m ∈ L` be the lamp with value `m_1` at `C`.
  - For `u ∈ N_0`, `φ(u)` is the lamp with value `u` at `C`. So `[φ(u), m] = 1` iff `u ∈ C_Y(m_1)`, that
    is, iff `u ∈ ⟨x_n⟩`.
- **Two realized subgroups.** Let `P ∈ B_A` contain `T_n`, by `(B_n)`.
  - `D_1 = {g ∈ T_n : [φ(g), m] = 1}` is realized. Embed `T_n` diagonally in `P × L` by `g ↦ (g, φ(g))`,
    and take `(1, m)`.
  - `D_2 = C_(T_n)(x_n)` is realized, with `m = x_n` in `P`.
- **Computing D_2.** `x_n` lies in the vertex group `Y` of the Bass–Serre tree of `G *_C Y`. It fixes an
  edge `yC` at that vertex only if `y^-1 x_n y ∈ C`. But `N_0` is normal in `Y`, and `N_0 ∩ C = 1`. So
  `x_n` fixes exactly one vertex, and its centralizer lies in the stabilizer `Y`. Hence
  `D_2 = C_Y(x_n) = N_0`.
- **(R_n).** `D_1 ∩ D_2 = {u ∈ N_0 : [φ(u), m] = 1} = ⟨x_n⟩`, and it is realized by item 5. ∎

## Scope

- **Other chains.** The same induction works for chains of `BS(1, k_i)` with any `|k_i| >= 2`. The inputs
  are `BS(1,k) ∈ B_A` (linear), and realization of the base generator of `BS(1,k)`. That realization is
  proved on main only for `k = 2`, so only `k_i = 2` is claimed.
- **Trees of chains.** A tree of such steps also works: any finite tree in which each new vertex group
  `BS(x, y)` is glued along a generator `x` realized in the current group. Only the linear chain is
  written out here.
- **Not claimed.** Nothing is claimed for cyclic chains (`H_n`, including Higman's `H_4`), or for the
  bi-infinite chain with its shift (`BG`). The induction runs **from the top of a tower**: each step
  wreaths over the group built so far. A cycle or a shift would need the step to be compatible with an
  automorphism, and that is not provided.

## Lesson for general BH

**Realization propagates through quotients.** Once `G ∈ B_A`, realized subgroups include:
- centralizers;
- finite intersections of realized subgroups;
- preimages `φ^-1(C_L(m))` for any homomorphism `φ` into a `B_A` group, via the diagonal embedding.

This lets one cut the new vertex group of an amalgam down to a cyclic subgroup, by pulling back a lamp
from the twisted lamplighter quotient. So the wreath trick and the centralizer trick feed each other, and
graph-of-groups towers of Baumslag–Solitar type climb to any finite height. What resists is **global
symmetry**. For `H_4` and `BG` the difficulty is not any finite piece of the tower. It is an automorphism
(the cyclic rotation, or the shift) that the top-down wreath construction must respect.
