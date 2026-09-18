---
rg: 2
id: triangular-subgroups-of-nv-contain-no-heisenberg-or-sl3z
kind: claim
title: Every infinite-order element of nV that preserves the coordinate flag has a periodic orbit with nonzero offset, so no conjugate of the triangular subgroup contains a Heisenberg centre, a BS(1,k) base element or an SL_3(Z) root element
distinct_from:
  heisenberg-in-nv-forces-drift-free-central-element: that proves that Heisenberg centres and BS(1,k) base elements of nV are drift-free and notes that the nonzero-drift hypothesis fails in nV for n >= 2; this proves the hypothesis holds on the triangular subgroup of nV for every n.
  infinite-order-elements-of-v-have-hyperbolic-periodic-points: that is the case n = 1 and is the base of the induction here.
  thompson-v-has-no-heisenberg-subgroup: that is the n = 1 statement for V; this covers the fibred, flag-preserving subgroups of every nV, including V^n and the lamplighter-type C(C,V) ⋊ V in 2V.
---

**ESTABLISHED** by `triangular-nv-periodic-offset-induction-proof`
(2026-09-17, unreviewed by a verifier lane).

**Setting.** Let `C = {0,1}^ω`, let `π_i : C^n → C^i` be the projection to the
first `i` coordinates, and let `s_g` be the offset cocycle of
`heisenberg-in-nv-forces-drift-free-central-element`. The **triangular subgroup**
`T_n ≤ nV` is the set of `g ∈ nV` such that, for every `i < n`, both `g` and
`g^-1` map fibres of `π_i` into fibres of `π_i`. Every such `g` has the form

`g(x_1, …, x_n) = (h_1(x_1), h_2^{x_1}(x_2), …, h_n^{x_1…x_{n−1}}(x_n))`

with every `h_i^{…} ∈ V`, each depending on its parameters through finitely many
values. Conversely, a map of this form lies in `T_n` whenever it lies in `nV`,
for instance when each parameter dependence is constant on the bricks of a
dyadic partition. `T_n` is a subgroup. It contains `V^n`, the group
`C(C, V) ⋊ V` of locally constant `V`-cocycles over `V` when `n = 2`, and its
iterates. The coordinate permutations of `nV` carry `T_n` to the triangular
subgroups for the other coordinate orders.

**Theorem.** Let `n >= 1`.

1. Every `g ∈ T_n` has a periodic point. If `g` has infinite order, there are
   `p ∈ C^n` and `k >= 1` with `g^k(p) = p` and `s_{g^k}(p) ≠ 0`.
2. Consequently, every infinite-order `g ∈ T_n` has a `g`-invariant atomic
   probability measure with nonzero drift. By item 1 of
   `heisenberg-in-nv-forces-drift-free-central-element`, `g` is undistorted in
   `nV`.
3. Let `f ∈ nV`. No nontrivial central element of a subgroup
   `H_3(Z) ≤ nV` lies in `f T_n f^-1`. No nontrivial element of `⟨x⟩` for a
   subgroup `BS(1,k) = ⟨x, t⟩ ≤ nV` with `|k| >= 2` lies there either. For
   `d >= 3` and any embedding `SL_d(Z) → nV` or `GL_d(Z) → nV`, no nontrivial
   power of any root element `e_ij` maps into `f T_n f^-1`.

**Where the triangular class dies.** A candidate embedding of `GL_3(Z)` into
`2V` built fibrewise, with a `V`-action on one coordinate and a locally
constant `V`-cocycle on the other, dies at the root element `e_13`. Its image
would have a periodic orbit with nonzero offset, from the induction on the
flag. But `e_13 = [e_12, e_23]` commutes with both factors, so it must be
drift-free. The invariant is the offset vector of a periodic orbit.

**What survives.** Callard–Salo's distortion element of `mV`
(`brin-thompson-mv-contains-a-distortion-element`) is drift-free, so it lies in
no conjugate of any `T_m`. An `SL_3(Z)` in `2V` must use elements that mix the
coordinates, as the baker's map does. The baker's map maps vertical fibres into
fibres, but its inverse does not.
