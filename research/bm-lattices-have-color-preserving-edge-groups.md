---
rg: 2
id: bm-lattices-have-color-preserving-edge-groups
kind: claim
title: Every torsion-free, edge-transitive, non-residually-finite lattice F_a *_{F_e} F_b on T' × T_d has a subgroup of index at most 2 of the same kind whose edge group, after conjugation in Aut(T_d), is color-preserving (lies in the right-angled Coxeter group W_{lk(D)}), so the wall-twist hypothesis of twisted-davis-amalgams-keep-hyperplane-data can be met
---

**ESTABLISHED** (lane proof, elementary, not reviewed). This answers the existence question left open in
item 5 of the required node.

## Statement

Let `Γ ≤ Aut(T') × Aut(T_d)` be a torsion-free cocompact lattice that acts edge-transitively and
without inversions on `T'`. Write `Γ = F_a *_{F_e} F_b` for the stabilizers of an edge and its endpoints,
and assume `pr_{T_d}` is injective on `Γ`. A **legal coloring** of `T_d` is an edge coloring with `d`
colors in which each vertex sees every color once. `W_{lk(D)} ≅ (Z/2)^{*d}` is the group of
color-preserving automorphisms for a fixed legal coloring.

1. **Criterion.** A torsion-free lattice `F ≤ Aut(T_d)` is conjugate into `W_{lk(D)}` iff the finite graph
   `F\T_d` is loopless and `d`-edge-colorable. This holds whenever `F` preserves the bipartition of `T_d`.
2. **Passage to index at most 2.** Let `β: Γ → Z/2` record whether an element swaps the bipartition of
   `T_d`.
   - If `β(F_e) = 0`, then `Γ` itself has `F_e` conjugate into `W_{lk(D)}`.
   - Otherwise `Γ_1 := ker β` has index 2. It is again torsion-free, edge-transitive without inversions
     on `T'`, non-residually finite if `Γ` is, and injective on `T_d`. Its edge group is `F_e ∩ ker β`,
     which is conjugate into `W_{lk(D)}`.
3. **Inputs exist.** Burger–Mozes give virtually simple torsion-free `(2m, 2n)`-groups in
   `U(Alt(2m)) × U(Alt(2n))` with dense projections (`m >= 109`, `n >= 150`; Radu arXiv:1712.01091 l.243).
   Radu gives torsion-free virtually simple `(6,8)`- and `(8,6)`-groups (l.2273).
   - A `(d_1,d_2)`-group acts on `T_{d_1}` with one edge orbit and with inversions. Its subgroup
     preserving the bipartition of `T_{d_1}` has index 2 and acts edge-transitively without inversions.
   - So with `d = d_2` (for example `d = 6, 8` or `2n`), items 1–2 produce the input needed by wall
     twists.
   - `pr_{T_d}` is injective because the kernel is a discrete normal subgroup of a just-infinite group
     whose projection is non-discrete.

## Proof

1. **Criterion.**
   - (⇐) Lift a proper `d`-edge-coloring of `F\T_d` to `T_d`. It is legal and `F`-invariant.
   - (⇒) An `F`-invariant legal coloring descends to the quotient. A loop would give a vertex two
     edges of the same color.
   - **Conjugation.** Any two legal colorings of `T_d` differ by an automorphism, built ball by ball.
     Conjugating by it makes `F` color-preserving for the standard coloring, i.e. `F ≤ W_{lk(D)}`.
   - **Bipartition.** If `F` preserves the bipartition, `F\T_d` is bipartite (so loopless) and
     `d`-regular. By König's theorem it is `d`-edge-colorable.
2. **Passage to index at most 2.**
   - **Transitivity.** Suppose `β(F_e) ≠ 0`. Then `β(F_a) = β(F_e) = β(F_b) = Z/2`, so
     `(F_a ∩ ker β) F_e = F_a`. Hence `F_a ∩ ker β` is transitive on the link of its vertex, and
     likewise for `F_b`.
   - **Edge-transitivity.** Every vertex of `Γ_1\T'` therefore has exactly one incident edge. Since
     `Γ_1\T'` is connected, it is a single edge, and `Γ_1 = (F_a ∩ ker β) *_{F_e ∩ ker β} (F_b ∩ ker β)`.
   - **Non-residual finiteness.** It passes to finite-index subgroups: `Γ_1 ⊇ Γ^(∞) = Γ_1^(∞)`.
   - **Coloring.** `F_e ∩ ker β` preserves the bipartition, so item 1 applies.
3. **Inputs exist.** The edge-transitivity of the bipartition-preserving subgroup is the transitive
   local action (`>= Alt(d_1)`) at a vertex of `T_{d_1}`.

## Caveat (parity)

- AL's universal group is `U(Alt_{2d-1})`. The section `E` of `hyperplane-extensions-into-davis-lattices-are-split`
  has local actions `(id_D, τ)`, which are even only when `τ` is even.
- Conjugating `F_e` to the standard coloring can change the parity of local actions from vertex to vertex.
- So to stay inside `U(Alt)` one must also check that `F_a` and `F_b` have even local actions in the new
  coloring. Otherwise one can work with `U(Sym_{2d-1}) = Aut(X_{O_d})`, which contains `U(Alt)` as a closed subgroup. AL's density theorem is proved only for `U(Alt)`.

## Lesson for general BH

- **The obstruction was bookkeeping.** "The input must be type-preserving on the carrier" costs at most
  an index-2 subgroup: bipartite quotients are always color-classifiable (König).
- **Inputs are cheap.** Non-residually-finite inputs for hyperplane embeddings come for free from any
  Burger–Mozes or Radu lattice. None of the difficulty of Kourovka 21.46 lies on the input side.
