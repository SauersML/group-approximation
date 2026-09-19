---
rg: 2
id: fp-stabilizer-engines-need-fp-vertex-groups
kind: claim
title: If the derived full group D(F_B) of Z/k * B on its compactified Bass–Serre tree is of type F_n (or FP_n), then so is the vertex group B; so a finitely presented stabilizer engine needs a finitely presented, decidable vertex group
distinct_from:
  fp-stabilizer-engines-need-decidable-vertex-groups: that derives solvability of the word problem of B from finite presentation of D(F_B); this derives finiteness of B (F_n, FP_n) from the same hypothesis. Together they say an fp engine needs B fp and decidable.
---

**ESTABLISHED** (lane proof, bh-emitter-b, 2026-09-18; elementary given the parent nodes;
one referee PASS, bh-ref-engines 2026-09-18, see Referee section).

**Notation.** As in `free-product-boundary-groupoids-carry-the-vertex-group-homology`:
- `k >= 2`, `B` is a finitely generated infinite group, and `D = Z/k * B`;
- `X` is the Bass–Serre tree of `D` compactified by its `B`-vertices;
- `F_B = [[D ⋉ X]]` and `D(F_B)` is its commutator subgroup.

The vertex `v = 1B` is an infinite emitter with germ group `B`.

## Statement

Let `n >= 1`. If `D(F_B)` is of type `F_n`, then `F_B`, `D` and `B` are of type `F_n`. The
same holds with `FP_n` in place of `F_n`. With `fp-stabilizer-engines-need-decidable-vertex-groups`,
a finitely presented `D(F_B)` forces `B` to be finitely presented **and** to have solvable
word problem.

## Proof

1. **From `D(F_B)` to `F_B`.**
   - By the parent node, `F_B/D(F_B)` maps onto `B_ab` with kernel of order at most 2. So
     it is a finitely generated abelian group, which has type `F_∞`.
   - An extension of a group of type `F_n` by a group of type `F_n` has type `F_n`, and
     likewise for `FP_n`.
2. **From `F_B` to `D`.**
   - `D <= F_B <= [[D | X]]`, with `X` compact and `D` finitely generated.
   - `D` is locally faithful at every point. A nonempty open subset of `X` contains three
     distinct ends. A tree automorphism fixing three ends fixes their median vertex and the
     three rays to them, hence an edge, and edge stabilizers in `T` are trivial.
   - So `piecewise-groups-quasi-retract-onto-a-locally-faithful-base` applies: `D` is a
     quasi-retract of `F_B` and inherits type `F_n` or `FP_n`. The retraction reads the
     label of an element at one point.
3. **From `D` to `B`.** `B` is a retract of `Z/k * B` (kill `Z/k`), and retracts inherit
   `F_n` and `FP_n`. `∎`

## Consequences

- **Track C with simple inputs is circular.** If `S` is a decidable simple group with
  `D(F_S)` finitely presented, then `S` is already finitely presented, so `S` itself
  witnesses Boone–Higman for its subgroups. The claim
  `simple-inputs-have-finitely-presented-stabilizer-engines` is false; see
  `stabilizer-engines-of-non-fp-simple-groups-are-not-fp` for an explicit decidable
  counterexample.
- **The emitter gate only concerns fp germ groups.** For stabilizer engines, finiteness at
  the infinite emitter `v` can hold only when the germ group `B` is finitely presented and
  decidable. Both conditions are necessary. Whether they suffice is
  `fp-decidable-vertex-groups-have-fp-stabilizer-engines`, which implies Boone–Higman.
  Reid's group (`B = Z`) is its first case.
- **Higher finiteness.** An `F_∞` engine needs `B` of type `F_∞`.

## Lesson for general BH

At an infinite emitter the germ group is a quasi-retract of the host whenever the labels
act locally faithfully. So an emitter cannot absorb an input's lack of finite presentation.
It can only be a place where an already finitely presented, decidable group is made simple.
The emitter gate (IE) is therefore a problem about finitely presented germ groups, and the
two necessary conditions (finite presentation and decidability) are exactly those of the
Boone–Higman conjecture for the vertex group.

## Referee (bh-ref-engines, 2026-09-18): PASS

- Step 1 holds: `F_B/D(F_B)` is finitely generated abelian, and extensions preserve `F_n`.
- Step 2 holds: `D` is locally faithful everywhere, since three ends in any open set force an
  element fixing that set to fix an edge, and edge stabilizers are trivial.
- Step 3 holds: `B` is a retract of `Z/k * B`.
- Now subsumed by the isolation and collapse theorems (`free-product-emitter-full-groups-need-isolated-vertex-groups`,
  `stabilizer-engines-need-torsion-vertex-groups`), which the collapse node itself uses.
