---
rg: 2
id: stabilizer-engines-die-over-groups-with-infinite-order-elements
kind: claim
title: The stabilizer engine F_B (and D(F_B)) is not finitely presented for any infinite finitely generated B in which the trivial subgroup is a limit of nontrivial subgroups, e.g. any B with an element of infinite order, isolated or not; the reason is that Z/2 * B is a limit of the amalgams B *_H (H x Z/2) as H -> 1
requires:
  - free-product-boundary-groupoids-carry-the-vertex-group-homology
  - free-product-emitter-full-groups-need-isolated-vertex-groups
  - stabilizer-engines-of-non-fp-simple-groups-are-not-fp
invalidates:
  - isolated-vertex-groups-have-fp-stabilizer-engines
distinct_from:
  free-product-emitter-full-groups-need-isolated-vertex-groups: that perturbs the vertex group B through its nearby marked groups, which forces B isolated and says nothing when B is isolated; this perturbs the acting group Z/2 * B through amalgams that keep B, which kills isolated B too (Thompson's F, T, V, every infinite fp simple group).
  stabilizer-engines-are-fp-only-over-isolated-groups: the same as the previous entry.
  v-stabilized-stabilizer-engines-are-never-finitely-presented: that kills the Cuntz-stabilized engines; this kills the plain (V-less) engines D(F_B) themselves.
---

**ESTABLISHED** (lane proof, bh-free-56, 2026-09-18; elementary given Nekrashevych's theorem
and the parent nodes; not reviewed; no priority claimed).

**Notation.** As in `free-product-boundary-groupoids-carry-the-vertex-group-homology` with
`k = 2`: `A = <a> ≅ Z/2`, `B` infinite and finitely generated, `D = A * B`, `T` its Bass–Serre
tree with the `A`-vertices suppressed, `X` the tree compactified by its `B`-vertices, and
`F_B = [[D ⋉ X]]`. For `u ∈ D`, `h(u)` is the half-tree of the edge `uA` on the side of `uB`.

## Statement

Suppose `B` has nontrivial subgroups `H_n` with `H_n ∩ F = ∅` for every finite `F ⊂ B − {1}`
and all large `n`. That is, `1` is not isolated in the Chabauty space `Sub(B)`. Then neither
`F_B` nor `D(F_B)` is finitely presented.

**When the hypothesis holds.**
- If `g ∈ B` has infinite order, take `H_n = <g^{N_n}>`, where `N_n` exceeds every exponent `e`
  with `g^e` in the `n`-ball.
- If `B` has infinitely many elements of prime order, take `H_n = <h_n>` with `h_n` of prime
  order outside the `n`-ball.
- So the hypothesis covers every infinite finitely presented group now known: an infinite
  finitely presented torsion group is not known to exist.

**Consequence.** `isolated-vertex-groups-have-fp-stabilizer-engines` is false. It fails, for
example, at `B` = Thompson's `F`, `T` or `V`, which are isolated. So no plain stabilizer engine
over a group with an element of infinite order is finitely presented, whatever its vertex group.

## Proof

**The approximating actions.** Put `D_n = B *_{H_n} (H_n × A)`: add to `D` the relations
`[a, h] = 1` for `h ∈ H_n`.
- `π_n : D → D_n` is a quotient map.
- The Bass–Serre tree `T_n` of `D_n` has `B`-vertices `D_n/B` and `(H_n × A)`-vertices of
  valence 2. We suppress the latter, so edges are `D_n/(H_n × A)`.
- At `1B` the edges are indexed by `B/H_n`, an infinite set. If it were finite, use the ends
  only; the index grows with `n`.
- Let `X_n` be `T_n` compactified by its `B`-vertices, and `h_n(v)` the half-tree of the edge
  `v(H_n × A)` on the side of `vB`. Then `π_n(d)·h_n(π_n u) = h_n(π_n(du))`.
- `Φ_n` is the group of homeomorphisms of `X_n` that are piecewise given by elements of `D_n`
  on finitely many clopen pieces.

**Step 1: bounded configurations transfer.** Let `U ⊂ D` be finite. For large `n`, every
Boolean combination of the half-trees `h(u)`, `u ∈ U`, is empty in `X` iff the same
combination of the half-trees `h_n(π_n u)` is empty in `X_n`.
- *Normal forms.* Write `u^{-1}u' = b_0 a b_1 a ⋯ a b_m` in normal form, with interior
  `b_i ≠ 1`. The relative position of `h(u)` and `h(u')` depends on three things:
  - whether `u^{-1}u' = 1`;
  - whether `b_0 = 1`;
  - whether `b_m = 1`.

  The position is one of equal, complementary, nested, disjoint or co-disjoint.
- *The same holds in `D_n`,* with "`∈ H_n`" in place of "`= 1`", because `π_n(u^{-1}u')`
  has the amalgam normal form with the same syllables.
- *Choice of `n`.* Take `n` so large that `H_n` avoids the finitely many nontrivial syllables
  that occur. Then all pairwise positions agree.
- *Atoms.* A Boolean atom is nonempty iff it contains a vertex, since from a vertex one can
  walk out along uncut edges. By Helly's theorem for subtrees, that holds iff the half-trees
  involved meet pairwise. So atom emptiness agrees.

**Step 2: transfer of words.** Fix a finite generating set `S` of `F_B` containing `a` and
generators of `B`, each given by (piece, label) data. Read the data in `D_n` to get `s_n`.
- For large `n`, `s_n ∈ Φ_n`: its partition identities are Boolean statements, and they
  transfer by Step 1.
- For `a` and the generators of `B`, `s_n` is the action of `π_n(s)`.
- Let `w` be a word in `S`, and compute its data formally.
- *If `w = 1` in `F_B`,* every nonempty atom has label `1` in `D`: `D` acts locally faithfully
  on `X` (`fp-stabilizer-engines-need-fp-vertex-groups`, step 2). Its image is `1` in `D_n`. The
  atoms of `X_n` are the images of the atoms of `X`. So `w_n = 1`.
- *If `w ≠ 1`,* some nonempty clopen `V` in the data satisfies `wV ∩ V = ∅`. This is a
  Boolean statement about finitely many half-trees, so it transfers. So `w_n ≠ 1` for large
  `n`. No faithfulness of `D_n` is needed.

**Step 3: contradiction.** Suppose `F_B = <S | R>` with `R` finite.
- By Step 2, for large `n` the relators hold in `Φ_n`. So `s ↦ s_n` defines a homomorphism
  `φ_n : F_B → Φ_n`, and `φ_n|_D` is `π_n` followed by the action on `X_n`.
- Pick `1 ≠ h ∈ H_n`. Then `[a, h] ≠ 1` in `D ≤ F_B` (normal form `a h a h^{-1}`), and
  `φ_n([a, h]) = π_n([a, h]) = 1`. So `ker φ_n ≠ 1`.
- `D ⋉ X` is minimal (parent node). By Nekrashevych (arXiv:1511.08241, main theorem), every
  nontrivial normal subgroup of `F_B` contains the alternating group `A(F_B)`, which is
  nontrivial.
- Fix `1 ≠ x ∈ A(F_B)`. Then `φ_n(x) = 1` for every large `n`, but `φ_n(x) = x_n ≠ 1` for
  large `n` by Step 2. This is a contradiction.
- Finally, if `D(F_B)` were finitely presented then so would be `F_B`
  (`fp-stabilizer-engines-need-fp-vertex-groups`, step 1). `∎`

**Calibration.**
- Finite `B` has `1` isolated in `Sub(B)`. Its engines are Higman–Thompson-type groups and
  finitely presented, so there is no conflict.
- For `B = Z` this re-proves that Reid's group is not finitely presented, now without the
  quotients `Z/n` (`free-product-emitter-full-groups-need-isolated-vertex-groups`).
- Step 2 and Step 3 use only relations of bounded size. The new relations `[a, h]` are long,
  since `h` leaves every ball. That is why the amalgams converge to `D`.

## Lesson for general BH

**Perturb the whole acting group, not just the germ group.** A free product `A * B` is a limit
of the amalgams `B *_H (H × A)` as `H → 1`. These amalgams are proper quotients, and they keep
the same kind of tree and the same bounded configurations. So a tree-boundary full group of a
free product with an infinite factor is never finitely presented, whatever the factor is. The
only possible exception is a factor with `1` isolated in `Sub(B)`, for example an infinite
torsion group with finitely many elements of prime order.

More generally, suppose a finitely presented host has a persistent monolith, as full groups of
minimal groupoids do. Then its acting group must be isolated among the quotients that preserve
bounded configurations of the space. A free product never is. That is the precise sense in which
emitters are dead: "infinite isotropy permuting infinitely many branches freely" always admits
the perturbation "let a long element of the isotropy fix a branch". The survivors are hosts
whose acting group has no such configuration-preserving quotients. That is rigidity in the
sense of the master route: non-local emptiness (SFT constraints), or acting groups that are
themselves isolated with a rigid action.
