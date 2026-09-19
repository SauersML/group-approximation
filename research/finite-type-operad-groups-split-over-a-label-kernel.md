---
rg: 2
id: finite-type-operad-groups-split-over-a-label-kernel
kind: claim
title: In a finitely generated operad with transformations, transformations act on the finite sets of classes of each degree, so the transformation groups are residually finite modulo a class-trivial part, and that part only contributes a label kernel of the operad group
distinct_from:
  finitely-coded-unit-groups-act-residually-finitely: that is the unit-group statement for Li-coded groupoids; this is the operad-with-transformations version, including abstract (non-topological) operads, where the class-trivial part need not vanish.
  wreath-recursion-thompson-groups-inherit-fn: that identifies V(B, psi) with V(B/J) through the dying kernel; here the same phenomenon is the label kernel, and the calibration recovers that identification.
---

Inputs this claim recorded under the older schema (not a proof; they do not establish it): `thumann-operad-groups-need-only-f-infinity-transformations`.

**Status.**
- **Part A: ESTABLISHED** (lane bh-invent-07, 2026-09-18; elementary lane proof, not reviewed).
- **Part B: lane proof sketch.** One step, (R) below, is only checked in the calibration cases and
  the topological case.
- No priority claimed.

The terminology is Thumann's (arXiv:1409.1085), as in
`thumann-operad-groups-need-only-f-infinity-transformations`.

## Part A (established)

Let `𝒪` be a planar, symmetric or braided operad with transformations that is finitely generated,
i.e. has finitely many very elementary classes. For a color `c` and a degree `k`, let `C_k(c)` be the
set of one-sided transformation classes of degree `k` with output `c`.

1. `Aut_ℐ(c)` acts on the right on each `C_k(c)` by `[θ]·h = [θ*h]`. Every `C_k(c)` is finite.
   This is steps 1 and 3 of the claim in `thumann-operad-groups-need-only-f-infinity-transformations`,
   where only finite generation is used.
2. Let `K_∞(c)` be the kernel of the action on `⊔_k C_k(c)`, the **class-trivial** transformations.
   Then `Aut_ℐ(c)/K_∞(c)` embeds in `∏_k Sym(C_k(c))`, so it is residually finite.
3. So every subgroup of `Aut_ℐ(c)` with no nontrivial finite quotient lies in `K_∞(c)`. Examples:
   infinite finitely generated simple groups, including simple Kazhdan groups, divisible groups, and
   non-residually-finite groups with no finite quotients.
4. **The topological case.** Suppose `𝒪` is a suboperad of `End(TOP, ⊔)` on compact spaces, and the
   image pieces of the operations with output `c` form a basis of `c`.
   - An `h ∈ K_∞(c)` maps every piece of every operation onto a piece of the same operation.
   - The subgroup fixing each piece of each composite of degree at most `n` has finite index in
     `K_∞(c)`.
   - The intersection of these subgroups fixes every basic open set, so it is trivial.
   - Hence **`Aut_ℐ(c)` itself is residually finite**. This is the operadic form of
     `finitely-coded-unit-groups-act-residually-finitely`, and needs only finite generation.

## Part B (lane sketch): the label kernel

Let `𝒯_K` be the transformations with trivial permutation or braid part whose degree-1 components lie
in `K_∞`. Let `Γ = π_1(𝒪, X)`, and let `L ⊆ Γ` be the set of loops `θ^{-1} α θ`: down along an
operation `θ` into `X`, apply `α ∈ 𝒯_K` on the leaves, back up along `θ`.

**(R), pure pull-through.** For a leaf label `k ∈ K_∞(c)` and an operation `ψ` with output `c`, one
has `ψ*k = β*ψ` with `β ∈ 𝒯_K` on the inputs of `ψ`.
- **Topological case:** `K_∞ = 1` by A4, so there is nothing to check.
- **Röver–Nekrashevych calibration (below):** it holds, since class-trivial elements fix every vertex,
  so all their sections are class-trivial.
- **General abstract operads:** the permutation part of `β` must be shown trivial, using
  class-triviality on all composites `φ*ψ` and right cancellativity. This is the step that is not
  checked in general.

Assuming (R), in the cancellative calculus of fractions:
1. **`L` is a directed union of subgroups.** Each subgroup `θ^{-1} 𝒯_K(dom θ) θ` is isomorphic to a
   finite product `∏_j K_∞(c_j)`, because the category embeds in its groupoid of fractions. These
   subgroups are directed under refinement by (R) and square filling.
2. **`L` is a normal subgroup, and exactly the kernel of `Γ → Γ' := π_1(𝒪/𝒯_K, X)`.**
   - The quotient operad `𝒪/𝒯_K` has transformation groupoid `ℐ/K_∞`, which is residually finite
     by A2.
   - `L ⊆ ker`, since `𝒯_K` maps to identities.
   - Conversely, suppose `a^{-1}b` dies in `Γ'`. After a common refinement `Ψ`, the arrows `Ψ*a` and
     `Ψ*b` agree up to some `α ∈ 𝒯_K`. Then `a^{-1}b = (Ψ*b)^{-1} α^{±1} (Ψ*b) ∈ L`.

So `1 → L → Γ → Γ' → 1`: the operad group is an extension of an operad group with residually finite
transformations by a locally-(products of `K_∞`) label group.

**Consequences, conditional on (R):**
- **Simple subgroups.** Every finitely generated simple subgroup `S ≤ Γ` either maps injectively
  into `Γ'` or lies in `L`. In the second case `S` embeds in a single `K_∞(c) ≤ Aut_ℐ(c)`: `S` lies in
  one term `∏ K_∞(c_j)`, and some projection is injective because `S` is simple.
- **Transformations without finite quotients.** A group `G ≤ Aut_ℐ(c)` with no finite quotients lies
  in `L`. If `Γ` is simple and some such `G` survives in `Γ`, then `Γ = L`. Since `Γ` is finitely
  generated, `Γ` then lies in one finite product of `K_∞`'s, and the operad's dynamics contributes
  nothing.

## Calibration

Take `B` with a wreath recursion `ψ : B → B ≀ S_d`, and the abstract monochromatic operad with
`ℐ = B`, generated by one split `θ` with `θ*b = ψ(b)*θ` (the cloning category of
`wreath-recursion-thompson-groups-inherit-fn`).
- The classes `C_k` are the `d`-ary forests. `B` acts on them through its action on the tree, so
  `K_∞ = K`, the kernel of the tree action.
- (R) holds.
- `L` is the label group of `K/J`, where `J` is the dying kernel, and `Γ/L ≅ V_d(B/K)`. Together with
  that node's `V(B, ψ) ≅ V(B/J)`, this recovers its criterion: `V(B, ψ) → V_d(G)` is an isomorphism
  iff `J = K`.
- If `B` contains a simple Kazhdan group `P`, which has no finite quotients, then `P ⊆ K`. So `P` is
  either killed (`P ⊆ J`) or survives only as labels. Either way it never reaches the simple
  Röver–Nekrashevych group `V_d(G)`.

## Lesson for general BH

**Programmable finite-type operads are not a universal compiler through their transformations.**
- Finite generation already forces the transformation groups to act on finite sets of classes. So
  Thumann's finiteness engine sees only their residually finite quotient.
- A simple Kazhdan input, or any input with no finite quotients, placed among the transformations
  lands in the label kernel. It gains nothing: it is not in the simple part and not in the dynamics.
- A finite-type operad can host non-RF inputs only through its higher operations, over residually
  finite transformations. By the definability caps on main, those higher operations then need a
  non-tame rule.
- The escape is an operad with infinitely many elementary classes on which the transformations act
  oligomorphically. That is the twisted Brin–Thompson / actor shape, stated operadically in
  `oligomorphic-operads-have-f-infinity-groups`.
