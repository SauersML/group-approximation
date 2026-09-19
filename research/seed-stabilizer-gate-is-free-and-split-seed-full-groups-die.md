---
rg: 2
id: seed-stabilizer-gate-is-free-and-split-seed-full-groups-die
kind: claim
title: For a seed SFT the finitely generated stabilizer gate follows from finite generation of the full group, and a seed full group that splits over Γ is the lampshuffler of Γ, so it is not finitely presented for virtually indicable Γ although its boundary full group is
distinct_from:
  hard-evaluation-seeds-with-finitely-presented-full-groups: that is the open SEED existence statement with three conditions; this proves its third condition (finitely generated seed stabilizer) is implied by its second (finite presentation), and kills the split case of the second.
  seed-full-group-finite-presentation-lives-on-the-boundary: that proves finite presentation of the seed full group passes DOWN to the boundary full group; this shows it does not come back UP, by the split seeds, where the boundary group is Γ and the full group is the lampshuffler.
  fp-finitary-permutation-overgroups-are-type-a-actors: that is the general theorem for finitely generated overgroups of Alt_fin(X); this applies it to seed orbits.
  lampshuffler-groups-are-not-fp2-over-q: that is the theorem about FSym(X) x| G for free G-sets; this identifies which seed full groups are such lampshufflers.
---

**ESTABLISHED** by `seed-stabilizer-gate-proof` (elementary; lane proof, not independently
reviewed; no priority claimed).

## Setting

- `Γ` is an infinite finitely generated group, `A` a finite alphabet, `Y ⊆ A^Γ` closed and
  `Γ`-invariant (for instance an SFT).
- `y_* ∈ Y` is a seed: (S1) `y_*` is isolated in `Y`; (S2) `Stab_Γ(y_*) = 1`; (S3) the orbit
  `O = Γ·y_*` is dense in `Y`. Put `∂ = Y ∖ O`.
- `F = [[Γ ⋉ Y]]` is the topological full group: homeomorphisms `h` of `Y` with a locally
  constant `c: Y → Γ` and `h(y) = c(y)·y`. It contains `Γ` as the constant cocycles.

## Statement

1. **The stabilizer gate is free.** `F` acts faithfully on `O` and contains `FSym(O)`. If `F` is
   finitely generated, then `Stab_F(o)` is finitely generated for every `o ∈ O`, and `F` has one
   orbit on 2-subsets of `O`. So `F ↷ O` is of type (A) **iff `F` is finitely presented**.
   In `hard-evaluation-seeds-with-finitely-presented-full-groups`, condition 3 follows from
   condition 2.
2. **Split criterion.** The following are equivalent:
   - (a) `F = FSym(O) · Γ`;
   - (b) every `f ∈ F` agrees with some constant `γ ∈ Γ` outside a finite subset of `O`.
   When they hold, `F ≅ FSym(Γ) ⋊ Γ = Shuffler(Γ)`, the lampshuffler of `Γ`.
   They hold whenever `∂` is a single point.
3. **Split seeds die.** If (a) holds and some finite-index subgroup of `Γ` maps onto `Z`, then
   `F` is not of type `FP_2` over `Q`, so it is not finitely presented.
4. **Boundary finite presentation is not sufficient.** Take `Γ = Z` and `y_* = …0001000…`.
   Then `Y = O ∪ {0^Z}`, `∂` is one point, the boundary full group is `Z` (finitely presented),
   and `F = FSym(Z) ⋊ Z` is Houghton's `H_2`, which is not finitely presented.
   So the implication "`F` finitely presented ⇒ `F_∂` finitely presented" of
   `seed-full-group-finite-presentation-lives-on-the-boundary` has no converse. Finite
   presentation of `F` is not a property of the boundary alone: the extension
   `1 → FSym(O) → F → F_∂ → 1` is a separate gate.

## Consequence for SEED

The SEED hole is exactly two conditions: a hard forced seed (condition 1) and a finitely
presented full group (condition 2). Condition 2 cannot be checked on `∂` alone. A witness over a
virtually indicable `Γ` (for example `Z^2`, `F_2 × F_2`, any polynomial-growth `Γ` of positive
first virtual Betti number) must have a non-split full group: some element of `F` must follow
different elements of `Γ` near different parts of `∂` (for example an element of the alternating
full group of the boundary groupoid, when `∂` has room for one).
