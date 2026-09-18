---
rg: 2
id: cornulier-regime-coset-sfts-are-quantum-rigid
kind: claim
title: If Δ is finitely generated and Δ\Λ/Δ is finite, every subshift of right-Δ-invariant configurations is quantum rigid, and over a finitely presented Λ its crossed product is finitely presented
distinct_from:
  coset-invariant-sft-rigidity-descends-along-double-cosets: that is the general descent criterion; this is its zero-complexity case, where no determinism is needed.
  finitary-symmetric-extensions-of-oligomorphic-actions-are-fp: that is about groups FSym(Ω) ⋊ Λ; this is about crossed-product algebras of coset subshifts over the same kind of action.
---

**ESTABLISHED (lane proof, unreviewed; no priority claimed).** It follows from
`coset-invariant-sft-rigidity-descends-along-double-cosets` with `c ≡ 0`.

## Statement

Let `Λ` be finitely generated, and `Δ ≤ Λ` finitely generated with finitely many double cosets.
Let `R` be the largest span of a double coset, and `D ≥ max(D_0, R/2)`.
1. Every subshift `X ⊆ A^Λ` of right-Δ-invariant configurations is `D`-quantum rigid over every field.
2. If moreover `Λ` is finitely presented and `X` is an SFT, then `LC(X, k) ⋊ Λ` is a finitely
   presented `k`-algebra (`quantum-rigid-sfts-over-fp-groups-have-fp-crossed-products`).
3. The full coset shift `A^(Λ/Δ)` is such an SFT: it is cut out by the finitely many rules
   `x(λ) = x(λδ)`, `δ ∈ Σ_Δ`.

## Proof

Every pair of points of `Λ/Δ` has one of the finitely many types. Each has a representative of length
`≤ R ≤ 2D`, so part 2 of the descent theorem makes every pair commute. Parts 2 and 3 of the
statement are then the cited import and the observation above.

## Calibration

This is the algebra analogue of Cornulier's criterion for permutational wreath products
(Cornulier, Geom. Dedicata 2006; recalled, not re-read at source): `A ≀_(Λ/Δ) Λ` with `A ≠ 1` is
finitely presented iff `Λ` is finitely presented, `Δ` is finitely generated, and `Λ` has finitely many
orbits on `(Λ/Δ)^2`. There the lamps at two points commute by one relation per double coset. Here the
letter idempotents at two points commute for the same reason.

Instances:
- Thompson's `V` on the dyadic points of the Cantor set.
- `F` and `T` on dyadics.
- `CT_P(Z)` on `N_0` (`ct-p-z-acts-on-the-nonnegative-integers-with-type-a`).
- Every type (A) actor on its type (A) set, with Δ the point stabilizer.

## Why this does not finish gate G2

For `V`, `F`, `T` and `CT_P(Z)` the action has property (IS). So
`set-transitive-coset-shifts-have-only-constant-minimal-sets` puts a constant, Λ-fixed point in every
nonempty closed invariant set: none of these rigid SFTs is free, and none is minimal and infinite.

For a general type (A) action, (IS) is not known. One Cornulier-regime coset space with a free minimal
coset SFT would give a quantum rigid free minimal SFT at once, with no determinism. This is recorded
as `finite-double-coset-space-with-free-minimal-coset-sft`.

## Lesson for general BH

The Cornulier regime gives quantum rigidity for free: few pair types force commutation everywhere. It is
exactly the regime of type (A) actions, where Ramsey-type homogeneity kills freeness. The rigid free
minimal SFT (★) must therefore come from a coset space with infinitely many pair types, rigidified by
determinism.
