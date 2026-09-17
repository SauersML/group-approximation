---
rg: 2
id: tits-independence-vertex-groups-are-branch-type
kind: claim
title: Under Tits' independence property on a locally finite tree, ball fixators split as products of level rigid stabilizers, so vertex stabilizers are branch-type groups and a finitely presented Tits-(P) host with finitely presented edge stabilizers yields a finitely presented branch-type group
distinct_from:
  tits-independence-amalgams-force-self-product-edge-groups: that finds V x V inside the edge factor of a (P)-amalgam; this identifies the whole vertex stabilizer as a branch-type group and transfers finite presentability to it, reducing the locally finite Tits route to the existence of finitely presented branch-type groups.
  micro-supported-tree-actions-self-embed-rigid-stabilizers: that gives infinite direct sums in rigid stabilizers for any micro-supported tree action; this uses local finiteness and (P) to get finite index products at every level of a vertex stabilizer.
  profinite-tree-hosts-make-fa-subgroups-residually-finite: that makes FA subgroups of faithful locally finite tree hosts residually finite and excludes non-residually-finite FA inputs; this is structural, and says the vertex groups of a (P)-host are branch-type and, for finitely presented hosts, finitely presented, whatever the input.
  bliw-locally-finite-tree-actions-embed-in-fp-simple-groups: that embeds groups acting on locally finite trees in finitely presented simple groups by other means; this constrains hosts whose simplicity comes from Tits' theorem on the tree itself.
---

**ESTABLISHED (unreviewed).** Proof: `tits-independence-vertex-groups-are-branch-type-proof`.

**Setting.** A group `Γ` acts faithfully and without inversions on a locally
finite tree `T`. It has Tits' property (P) edge by edge: for every oriented edge
`f = (x, y)`,

`Γ_f = R(Y_f) · R(Y_{f̄})`,

where `Y_f` is the half-tree on the `y` side and
`R(Y) = {g ∈ Γ : g fixes every vertex outside Y}`. For a vertex `v` and `r ≥ 1`,
let `B_r(v)` be the ball of radius `r`, and let `E_r(v)` be the finite set of edges
`f = (x, y)` with `d(v, x) = r − 1` and `d(v, y) = r`. View `(T, v)` as a rooted
tree. For `y ∈ S_r(v)` with last edge `f`, the rigid stabilizer in `Γ_v` of the
subtree below `y` is exactly `R(Y_f)`.

**Theorem.**

1. **Ball fixators split.** For every vertex `v` and every `r ≥ 1`,

   `Fix_Γ(B_r(v)) = ∏_{f ∈ E_r(v)} R(Y_f)`,

   an internal direct product. It is a normal subgroup of finite index in `Γ_v`.
2. **Branch-type vertex groups.** `Γ_v` acts faithfully on the rooted tree
   `(T, v)`. For every level `r`, the product of the rigid stabilizers of the level-`r`
   vertices has finite index in `Γ_v`. `Γ_v` is residually finite, and so is
   every subgroup of `Γ` with property FA, since such a subgroup fixes a vertex.
3. **Branch groups under 2-transitivity.** Suppose every vertex stabilizer acts
   2-transitively on the neighbours of its vertex. Then `Γ_v` is transitive on
   every sphere `S_r(v)`. So `Γ_v` is a **branch group** in the sense of
   Bartholdi--Grigorchuk--Šunić: level-transitive, with finite-index level rigid
   stabilizers.
4. **Nontriviality.** Suppose the action is also minimal, fixes no end, `T` is
   not a line, and some edge stabilizer is nontrivial. Then every `R(Y_f)` is
   infinite and contains `⊕_N R(Y_f)`, by
   `micro-supported-tree-actions-self-embed-rigid-stabilizers`. So the branch
   structure is non-degenerate.
5. **Finite presentability transfers.** Suppose `Γ` is finitely presented, the
   action is minimal, and edge stabilizers are finitely presented. Then `T/Γ` is
   finite and every `Γ_v` is finitely presented.
6. **Reduction.** Let `Γ` be finitely presented with finitely presented edge
   stabilizers, acting faithfully on a locally finite tree with (P), minimally,
   with no fixed end, not on a line, and with some nontrivial edge stabilizer.
   Then every `Γ_v` is an infinite finitely presented group with a faithful
   branch-type action on a rooted tree. Under the local 2-transitivity of item 3,
   `Γ_v` is a finitely presented branch group. No finitely presented branch group
   is known, and whether one exists is an open question of Bartholdi, Grigorchuk
   and Šunić ("Branch groups", 2003).

**Consequence for `boone-higman-conjecture`.** Take a Tits-(P) route that embeds a
decidable `G` in a finitely presented `Γ` acting on a locally finite tree, and
gets simplicity from `Γ⁺` via Tits' theorem, with finitely presented edge
stabilizers.

- By item 6, the route must first produce a finitely presented branch-type group,
  which is a finitely presented branch group whenever the local actions are
  2-transitive, as in every standard Tits calibration.
- By item 2, it can never place in `Γ` an input with an infinite
  non-residually-finite FA subgroup, such as a decidable infinite simple Kazhdan
  group (`erf-groups-have-decidable-simple-kazhdan-hosts`).
- Hence the locally finite Tits route strictly reduces to the construction of
  finitely presented branch-type groups whose vertex-group amalgams satisfy (P).
  A Tits-(P) host that avoids this open problem needs infinite valence, or edge
  stabilizers that are not finitely presented.

**Calibration.**

- `Aut(T_d)`, `d ≥ 3`: item 1 is the familiar splitting of the ball fixator of
  the full automorphism group of the rooted tree. `Aut(T_d)_v` is a branch group,
  uncountable and not finitely generated, so item 5 is not contradicted.
- A free product `A * B` of finite groups: all rigid stabilizers are trivial, item 1
  reads `1 = 1`, and item 4 does not apply.
- The discrete case: if vertex stabilizers are finite, item 4 forces all edge
  stabilizers to be trivial. This is the last remark of
  `tits-independence-amalgams-force-self-product-edge-groups`.
