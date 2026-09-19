---
rg: 2
id: stabilizer-engines-need-finitely-discriminable-vertex-groups
kind: claim
title: If a finitely generated group B is not finitely discriminable (for example, B infinite and residually finite), then the stabilizer engine F_B of Z/k * B and its derived subgroup are not finitely presented; in particular Reid's d = 0 Higman–Thompson variant is not finitely presented
distinct_from:
  fp-stabilizer-engines-need-decidable-vertex-groups: that shows a finitely presented engine forces a solvable word problem for B; this shows it forces B to be finitely discriminable. Neither condition implies the other (Z is decidable and not finitely discriminable).
  simple-inputs-have-finitely-presented-stabilizer-engines: that is the sufficiency claim for simple B, already refuted by stabilizer-engines-of-non-fp-simple-groups-are-not-fp; simple groups are finitely discriminable, so this obstruction is not what refutes it.
  fp-decidable-vertex-groups-have-fp-stabilizer-engines: that conjectured D(F_B) finitely presented for every infinite finitely presented decidable B; B = Z refutes it here.
  free-product-emitter-full-groups-need-isolated-vertex-groups: proved independently at the same time; it gets the stronger conclusion that B is isolated (finitely presented and finitely discriminable) by perturbing B to nearby marked groups; this node gets the finite-discrimination half by quotients only, and adds the abstract schema of Remark 2.
  stabilizer-engines-are-fp-only-over-isolated-groups: a third independent proof of the isolation statement, by marked-group approximation.
---

**ESTABLISHED** (lane proof, bh-emitter-a, 2026-09-18; elementary; not reviewed). No
priority is claimed.

**Parallel proofs.** The same obstruction was found independently at the same time.
- `free-product-emitter-full-groups-need-isolated-vertex-groups` and
  `stabilizer-engines-are-fp-only-over-isolated-groups` both prove the stronger statement
  that a finitely presented engine forces `B` to be isolated.
- Read this node for two things they do not contain: the explicit transfer lemma along
  quotient maps (Lemma 1), and the abstract schema of Remark 2, with checkable hypotheses
  (a) and (b) for other host constructions.

**Notation.** As in `free-product-boundary-groupoids-carry-the-vertex-group-homology`:
- `k >= 2`, `A = Z/k`, `B` a finitely generated infinite group, and `D = A * B`.
- `T` is the Bass–Serre tree, and `X` is its set of ends together with its `B`-vertices.
- `F_B = [[D ⋉ X]]` is the stabilizer engine, and `D(F_B)` is its commutator subgroup.

Following Cornulier–Guyot–Pitsch (arXiv:math/0511714, Proposition–Definition, as quoted
in `fp-simple-groups-are-isolated`), `B` is **finitely discriminable** if some finite
`F ⊂ B − {1}` meets every nontrivial normal subgroup of `B`.

## Statement

If `B` is finitely generated and not finitely discriminable, then neither `F_B` nor `D(F_B)`
is finitely presented.

**Corollaries.**
1. **Reid's group.** `B = Z` and `k = 2` give Reid's group `G`
   (`reid-higman-thompson-variant-d-zero-abelianization`). Neither `G` nor `G'` is finitely
   presented. That settles item 5 of that node.
2. **Residually finite inputs.** The same holds for every infinite, finitely generated,
   residually finite `B`: `Z^n`, free groups, surface groups, every fg linear group. For
   finite `E ⊂ B − {1}`, residual finiteness gives a finite-index normal `N` with
   `N ∩ E = ∅`, and `N ≠ 1` because `B` is infinite.

## Coding

At a `B`-vertex `w` choose the representative `g_w` of `w = g_w B` whose normal form in
`A * B` is empty or ends with a letter of `A − {1}`.
- **Edge labels.** The edges at `w` are the `g_w b` with `b ∈ B`; call `b` the label of
  `g_w b` at `w`. Label the edges at an `A`-vertex by `A` in the same way.
- **The label rule.** If `d ∈ D`, then `d g_w = g_{dw} h` for a unique `h = λ_d(w) ∈ B`, so
  `d` maps the edge labeled `b` at `w` to the edge labeled `hb` at `dw`. Every `d` acts on
  labels at each vertex by a left multiplication.
- **Cones.** For a `B`-vertex `w` and a finite `E ⊂ B`, the cone `K(w, E)` is `w` together
  with every point whose geodesic from `w` leaves through an edge whose label is not in
  `E`.
  - Cones are clopen: the complement is a finite union of half-trees.
  - Every half-tree is a finite union of cones.
  - Hence every clopen set is a finite disjoint union of cones, and `d K(w, E) =
    K(dw, λ_d(w) E)`.
- **Freeness.** `D` acts topologically freely on `X`. A `d` fixing a nonempty open set
  fixes every end of some half-tree, hence fixes that half-tree and an edge in it, and
  edge stabilizers are trivial.
- **Atoms.** Let `Y` be a finite subtree that contains `v = 1B`, contains all `k`
  neighbors of each of its `A`-vertices, and has only `B`-vertices as leaves.
  - For each `B`-vertex `w` of `Y`, the atom is `A_w = K(w, L_Y(w))`, where `L_Y(w)` is
    the set of labels of the `Y`-edges at `w`. Then `X = ⊔_w A_w`.
  - A cone `K(w, E)` with `w ∈ Y` and `E ⊂ L_Y(w)` is *`Y`-adapted*. It is the union of
    the atoms `A_u` with `u = w` or with `u` reached from `w` through an edge whose label
    is not in `E`.
  - So a family of `Y`-adapted cones partitions `X` if and only if the corresponding
    sets of atoms partition the `B`-vertices of `Y`.
- **Tables.** A `Y`-table of `g ∈ F_B` is a partition of `X` into `Y`-adapted cones `C_j`,
  together with `d_j ∈ D`, such that `g = d_j` on `C_j` and each `d_j C_j` is `Y`-adapted.
  - Every `g` has a `Y`-table once `Y` is large. Take a partition into cones on which `g`
    is given by elements of `D`, and let `Y` contain the apexes, the neighbors in their
    excluded directions, and the same data for the image cones.
  - A table stays a table when `Y` is enlarged, and pieces may be split into smaller
    adapted cones.
  - By freeness, `d_j` is determined by `g` on any nonempty open subset of `C_j`.

## The transfer lemma

Let `N ⊴ B`, `Q = B/N`, and `π : B → Q`. Extend `π` to `D → D_Q = A * Q` and to
`T → T_Q`.
- **The target space.** `X_Q` is defined like `X` when `Q` is infinite. When `Q` is
  finite, `X_Q` is the end space of `T_Q`, a Cantor set once `|Q| >= 3`.
- **The target group.** `F_Q = [[D_Q ⋉ X_Q]]`. `D_Q` acts topologically freely on `X_Q`,
  by the same argument.

**Lemma 1.** For every finite `S ⊂ F_B` there is a finite `E_S ⊂ B − {1}` with the
following property. For every normal `N ⊴ B` with `N ∩ E_S = ∅`, there is an injective
map `Φ : S → F_Q` such that:
- `Φ(xy) = Φ(x)Φ(y)` whenever `x`, `y` and `xy` lie in `S`;
- `Φ(b) = π(b)` for `b ∈ S ∩ B`.

*Proof.*
- **Choosing `Y` and `Δ`.** Choose one finite subtree `Y` as above such that:
  - every element of `S` has a `Y`-table;
  - for each pair `x, y ∈ S`, some `Y`-table of `y` has every image piece `d_j C_j` inside
    a single piece `C′` of a `Y`-table of `x`, and `e(d_j C_j)` is `Y`-adapted, where `e`
    is the entry of `x` on `C′`.

  This is possible: split each `C_j` along the preimages under `d_j` of the pieces of
  `x`, which are cones, and enlarge `Y` to contain the data of all cones involved. Let
  `Δ ⊂ D − {1}` be the finite set of quotients `d^{-1}d′` of table entries (of the same
  or different elements of `S`) that differ on a common atom.
- **Choosing `E_S`.** Let `L` be the labels of all edges of `Y` together with `1`,
  enlarged by two further elements of `B` (only `B`-labels at `B`-vertices are meant).
  Take `E_S` to consist of:
  - `L^{-1} L − {1}`;
  - every `B`-letter in the normal forms of the elements of `Δ`.
- **What `N ∩ E_S = ∅` gives.**
  - `π` is injective on `L`. So normal forms of vertices of `Y` map to normal forms, and
    `w ↦ π(g_w)Q` is a label-preserving embedding `ι : Y → T_Q`. Its `B`-letters are
    labels along `Y`.
  - `|Q| >= |L|`, so every atom `ι A_w := K_Q(ιw, π L_Y(w))` is nonempty and contains
    ends. For a `Y`-adapted cone, write `ι K(w, E) := K_Q(ιw, π E)`.
  - `π(δ) ≠ 1` for every `δ ∈ Δ`, since normal forms survive.
- **Transfer of partitions.** Adapted cones are unions of atoms, cut out by the same
  subsets of `Y` on both sides. So `Y`-adapted partitions of `X` correspond to partitions
  of `X_Q`.
- **Transfer of tables.** `d g_w = g_{dw} h` maps under `π` to
  `π(d) π(g_w) = π(g_{dw}) π(h)`. So `π(d)` maps `ιK(w, E)` onto `ιK(dw, λ E)`.
  - Define `Φ(g) := π(d_j)` on `ι C_j` for each piece of a `Y`-table. The `ι C_j`
    partition `X_Q`, and so do their images `ι(d_j C_j)`. So `Φ(g)` is a bijection
    `X_Q → X_Q` that is piecewise in `D_Q`, and `Φ(g) ∈ F_Q`.
  - It does not depend on the table: two tables of `g` have equal entries on every atom
    of `Y`, by freeness.
- **Multiplicativity.** In the chosen tables, `xy = e d` on a piece `C` of `y`, where
  `y = d` on `C` and `x = e` on the piece containing `d C`. The same holds for
  `Φ(x)Φ(y)` on `ι C`.
- **Injectivity.** Suppose `Φ(x) = Φ(y)`.
  - On each atom `ι A_w` of `Y`, the entries `d`, `d′` of the two tables satisfy
    `π(d) = π(d′)` on a nonempty open set. By freeness of `D_Q`, `π(d^{-1}d') = 1`.
  - If `d ≠ d′`, then `d^{-1}d′ ∈ Δ`, so `π(d^{-1}d′) ≠ 1`, a contradiction. Hence
    `d = d′` on every atom, and `x = y`.
- **Elements of `B`.** An element `b ∈ S ∩ B` has the one-piece table `(X, b)`, since
  `X = K(v, ∅)`. So `Φ(b) = π(b)`. `∎`

## Proof of the statement

- **A local configuration.** Fix `c ∈ B − {1}` and let `U` be the half-tree of points reached
  from `v` through the edge labeled `c`. Let `w = caB` for some `a ∈ A − {1}`, a `B`-vertex
  in `U`. Its representative is `g_w = ca`, and its edge toward `v` has label `1`.
  - Pick distinct `b_1, b_2, b_3 ∈ B − {1}`, and let `H_i` be the half-tree beyond the edge
    labeled `b_i` at `w`. Each `H_i` lies in `U`.
  - `s = g_w b_2 b_1^{-1} g_w^{-1}` fixes `w` and maps `H_1` onto `H_2`. Let `x` be `s` on
    `H_1`, `s^{-1}` on `H_2` and the identity elsewhere. Define `y` from `H_2` and `H_3` in
    the same way.
  - Then `x, y ∈ F_B` are involutions supported in `U`.
  - `xy` cycles three half-trees, so `[x, y] ≠ 1`.
- **Displacement.** Every `n ∈ B − {1}` maps `U` onto the half-tree through the label
  `nc ≠ c`, disjoint from `U`. So `n x n^{-1}` commutes with `x` and with `y`. A direct
  expansion gives the double-commutator identity

      [[n, x], y] = [x^{-1}, y] = [x, y]  for every n ∈ B − {1}.     (*)

- **Suppose `F_B = ⟨Σ | R⟩` is a finite presentation.**
  - Let `r` bound the relator lengths, the lengths of words for fixed generators
    `β_1, …, β_s` of `B`, and the lengths of `x`, `y` and `[x, y]`.
  - Let `S` be the ball of radius `r`, and apply Lemma 1 to it.
  - Since `B` is not finitely discriminable, there is a normal `N ≠ 1` of `B` with
    `N ∩ E_S = ∅`.
- **Building `ψ`.** Every relator is a word of length at most `r` all of whose prefixes
  lie in `S`, and it equals 1. Multiplicativity then gives `Φ(σ_1) ⋯ Φ(σ_ℓ) = Φ(1) = 1`.
  So `σ ↦ Φ(σ)` extends to a homomorphism `ψ : F_B → F_Q`, and `ψ = Φ` on `S` by
  induction on length.
- **What `ψ` does on `B`.** `ψ(β_i) = Φ(β_i) = π(β_i)`, so `ψ|_B = π`, and `ψ(n) = 1` for
  every `n ∈ N`.
- **The contradiction.** Take `n ∈ N − {1}`. By `(*)`,
  `ψ([x, y]) = [[ψ(n), ψ(x)], ψ(y)] = 1`. But `[x, y] ∈ S − {1}` and `Φ` is injective on
  `S`, so `ψ([x, y]) = Φ([x, y]) ≠ 1`.
- **So `F_B` is not finitely presented.** If `D(F_B)` were finitely presented, then `F_B`
  would be, by item 1 of `fp-stabilizer-engines-need-decidable-vertex-groups`, since
  `(F_B)_ab` is finitely generated. `∎`

## Remarks

1. **The mechanism is continuity, not geometry.** The engine sees `B` only through its
   regular action on the branches at an infinite emitter, and that data is local. So
   `F_B` is a limit of the engines `F_{B/N}` along quotient maps that stay injective on
   balls.
   - A finitely presented group sends every such approximation through a genuine
     homomorphism.
   - That homomorphism kills `N`, and the double commutator `(*)` carries the kernel
     into a fixed ball.
   - For `B/N` finite, `F_{B/N}` is the full group of a finite-valence tree boundary (an
     SFT full group), so `F_B` is a limit of such groups.
2. **The general schema.** Let `B ↦ E(B) ⊇ B` be any construction satisfying:
   - (a) a transfer lemma like Lemma 1, restricting to `π` on `B`;
   - (b) fixed `x, y` with `[x, y] ≠ 1` and `[[n, x], y] = [x^{±1}, y]` for all but
     finitely many `n ∈ B − {1}`.

   Then `E(B)` can be finitely presented only if `B` is finitely discriminable, with the
   same proof.
   - **Lampshufflers.** The schema covers the lampshuffler `FSym(B) ⋊ B`, with transfer to
     `FSym(B/N) ⋊ B/N` and `x`, `y` transpositions near `1`. So the lampshuffler is not
     finitely presented for any fg `B` that is not finitely discriminable.
   - For `B = Z` this is Brown's theorem on the Houghton group `H_2`. For virtually indicable
     `B` the stronger non-`FP_2` statement is `lampshuffler-groups-are-not-fp2-over-q`.
   - The schema adds the non-indicable, non-finitely-discriminable cases.
3. **Isolated vertex groups.** By `fp-stabilizer-engines-need-fp-vertex-groups`, a finitely
   presented `D(F_B)` also forces `B` to be finitely presented. Together with this node,
   `D(F_B)` finitely presented implies that `B` is **isolated** in the sense of
   Cornulier–Guyot–Pitsch: finitely presented and finitely discriminable, hence also
   decidable.

## What this changes

- **Refuted: the stabilizer engine conjecture.** The conjecture
  `fp-decidable-vertex-groups-have-fp-stabilizer-engines` asserts that `D(F_B)` is finitely
  presented for every infinite, finitely presented, decidable `B`. `B = Z` satisfies those
  hypotheses, and `D(F_Z)` is not finitely presented.
  - The route `boone-higman-via-fp-stabilizer-engines` fails for the same reason whenever
    `B_0` is not finitely discriminable, because then neither is `B_0 ≀ Z/2`.
- **Corrected statement.** The right conjecture is
  `isolated-vertex-groups-have-fp-stabilizer-engines`: `D(F_B)` is finitely presented for
  every infinite isolated `B`.
  - By Remark 3 this would be a characterization.
  - The repaired route is `boone-higman-via-isolated-stabilizer-engines`. It starts from an
    isolated envelope of the input, the setting of Cornulier–Guyot–Pitsch Question 4
    (`every-decidable-group-embeds-in-an-isolated-group`). The same correction is recorded
    inside `boone-higman-via-fp-stabilizer-engines`.
- **Calibration.** Reid's group was the proposed first test. Its negative answer is forced
  by residual finiteness of `Z` and says nothing about isolated vertex groups.
  - Informative tests need isolated `B`.
  - Thompson's `F` qualifies: it is finitely presented and every nontrivial normal
    subgroup contains `[F, F]`.
  - So do `T` and `V`, which are finitely presented and simple.
- **Constraint: Track A′ compression codings.** Consider a coding whose emitter group
  enters only through local rules, so that it satisfies (a) and (b) of Remark 2. Such a
  coding can be finitely presented only if the emitter group is finitely discriminable,
  and, if the emitter group is finitely presented, isolated.
  - A Clapham envelope `Λ₁` at the emitter is therefore not enough. The coding needs an
    isolated envelope of the input.
  - Otherwise the coding must use global data about `Λ₁`, such as an automatic or
    finite-state structure.
  - BBMZ's hosts for hyperbolic groups do exactly that. They are finitely presented over
    free groups, which are residually finite, so their construction cannot satisfy (a).

## Lesson for general BH

Finite presentation is an open condition in the space of marked groups. A host
construction that depends only locally on its input inherits that openness: its finitely
presented outputs occur only at inputs isolated from their proper quotients, that is,
finitely discriminable ones.
- **Uniform local engines.** Stabilizer engines, lampshufflers, and emitter codings in
  which the input acts only by its regular action all fall under this.
- **Three independent necessary conditions.** A finitely presented stabilizer engine needs
  its vertex group to be finitely presented, decidable and finitely discriminable, that is,
  isolated.
- **Consequences.** The engine route is really a route from Cornulier–Guyot–Pitsch's
  Question 4 (an isolated envelope) to Boone–Higman. Calibrations on residually finite
  groups such as `Z` are uninformative, and they must be run on isolated groups such as
  Thompson's `F`, `T` and `V`.
