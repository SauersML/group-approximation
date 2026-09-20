---
rg: 2
id: ct-z-21-74a-base-splitting-is-torsion-hard
kind: claim
title: "Kourovka 21.74(a) and the base splitting: computing the splitting of Theorem R decides the torsion problem of CT(Z), which is open; YES is r.e. and NO is certified by a splitting with certified indecomposable components, so 21.74(a) is decidable wherever indecomposability has finite certificates (the positive ray, and every Conway-type prefix-code map); torsion-hardness alone does not transfer to 21.74(a), because finite order forces YES but infinite order does not force NO"
distinct_from:
  ct-z-kourovka-21-74a-reduces-to-base-coarse-structure: that proves 21.74(a) decidable given the splitting; this asks whether the splitting is computable, relates that to the torsion problem, and states what a halting reduction would need.
  ct-z-torsion-problem-and-the-brin-thompson-transplant: that records the torsion problem of CT(Z) as open and why the Belk–Bleak coding does not transplant; this shows that computing the splitting is at least as hard.
  ct-z-21-74a-reductions-must-move-coarse-components: that is the coarse-action barrier; this sharpens what a reduction must do after Theorem R.
---

**ESTABLISHED** for Propositions 1–3 (lane proof, bh-2174-rank2, 2026-09-19; elementary, not
reviewed). The last two sections are analysis, not theorems. Kourovka 21.74(a) stays **OPEN**
beyond the classes named here. No priority claimed.

## Proposition 1 (the splitting is torsion-hard)

For `g ∈ CT(Z)`, `g` has finite order iff `g` has a splitting Σ (in the sense of
`ct-z-kourovka-21-74a-reduces-to-base-coarse-structure`) with no components, i.e. `U = X`.

*Proof.* If `g^N = 1`, then `U = X` works. Conversely, if `g^N` has identity formulas on all of
`X`, then `g^N = 1`. ∎

So any algorithm that, given `g`, outputs a splitting (when one exists) decides the torsion problem
of `CT(Z)`. That problem is open (`ct-z-torsion-problem-and-the-brin-thompson-transplant`). It is
decidable on the positive ray (`ct-p-z-positive-ray-torsion-and-finiteness-are-decidable`), for
monomial elements (`ct-z-monomial-elements-have-decidable-torsion`), and on the copy of the
full-shift topological full group `[[σ_3]]` that Conway's map puts in `CT_{3}(Z)`, for elements given as
elements of `[[σ_3]]` (`conway-amusical-permutation-is-the-full-three-shift`). The last is because Barbieri–Kari–Salo
(arXiv:2303.17270) prove the torsion problem of the topological full group of a full `Z^d`-shift
undecidable **iff `d ≥ 2`**, and torsion is intrinsic to the group.

## Proposition 2 (certificates)

1. **YES is r.e.** Enumerate finite partitions of `Z` into residue classes. The image of a class
   under `g` is a computable finite union of classes, so "g permutes the partition" is a finite
   check.
2. **NO has a certificate shape.** By Theorem R, if `g` has a splitting Σ, then `g` is NO iff the
   finite search over Σ fails. Every condition on Σ is checkable except indecomposability of the
   components, a `Π_1` condition ("no `g^(Mt)`-invariant proper clopen subset, for every `t`").
   So NO is r.e. on any class where a splitting exists and indecomposability comes with finite
   certificates.
3. **Two such classes.**
   - The positive ray: revealing pairs certify Lemma A (the cone node).
   - Every Conway-type prefix-code map `α_{P,Q}` (item 3 of the Conway node, a lane proof). An
     explicit conjugacy to a full shift certifies that every power is mixing, so Σ = (`U = ∅`,
     `R_1 = X`). The answer is then a finite fibre computation: `g` is YES iff some nontrivial box
     partition of `Φ` is permuted by all piece formulas as one permutation, and Theorem R bounds its
     depth. For Conway's `α` the translation holonomy `y ↦ y + 2/3` makes the answer NO.

*Proof of 3.* A full shift conjugacy is a finite combinatorial fact here: the forward and backward
cylinders are explicit boxes, as in the Conway node's proof. Every power of a full shift is
mixing, which rules out invariant proper clopen sets. The rest is Theorem R. ∎

## Proposition 3 (torsion alone does not transfer)

Suppose `g_M` is a computable family with `g_M` of finite order iff `M` halts. Then:
- if `M` halts, `g_M` is YES (Proposition 1 and the ⇐ direction of the search: a finite-order
  element permutes a nontrivial box partition);
- if `M` does not halt, nothing follows. Infinite-order elements can be YES, e.g. any `g` with two
  disjoint invariant residue classes.

So an undecidable torsion family gives an undecidable instance of 21.74(a) only together with a
*NO-wrapper*: a computable `g ↦ h(g)`, preserving finite order, such that every infinite-order
`h(g)` has a splitting of the Conway kind, one mixing component with a fibre-killing holonomy.
The obvious wrappers fail: disjoint unions always create a YES partition, and composing with `α`
on a cylinder does not control the coarse algebra.

## What a halting reduction must do (analysis)

- **Where the hardness must sit.** By Theorem R and Proposition 2, an undecidable family must have
  base splittings whose indecomposability has no finite certificate. Fibre coding, neutral primes on
  a positive ray are excluded, and saddle dynamics alone does not suffice (Conway's `α`).
- **A source of undecidable torsion.** This would be a computable embedding into `CT(Z)` of a
  finitely generated group with undecidable torsion problem. Candidates are the elementary
  Turing-machine group, or finitely generated subgroups of `[[σ_{Z²}]]` (Barbieri–Kari–Salo), or
  Brin's `2V` (Belk–Bleak, arXiv:1405.0982). None is known to embed in `CT(Z)`. The one-dimensional
  copy `[[σ_3]]` that Conway coordinates give has decidable torsion, so Conway coordinates alone
  will not produce one.
- **The natural target.** A family whose base, when `M` never halts, is a single certified-mixing
  component (as for `α`), and which acquires an invariant clopen cycle when `M` halts. Both halves
  are base phenomena. No construction is known.

## Lesson for general BH

**For residue-class questions in `CT(Z)`, the only nonconstructive ingredient is indecomposability
of the base components.** YES is always certifiable. NO is certifiable wherever
indecomposability is, as it is for revealing pairs and for explicit full-shift conjugacies. So
decidability of 21.74(a) on a class is a question about certifying mixing-type properties of the
base action. Torsion-hardness of that base does not by itself make 21.74(a) hard.
