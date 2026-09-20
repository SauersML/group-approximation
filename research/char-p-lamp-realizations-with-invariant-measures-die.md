---
rg: 2
id: char-p-lamp-realizations-with-invariant-measures-die
kind: claim
title: "Hyperfinite class-kill for char-p Burger lamp realizations in nV: if the lifting subgroup preserves a probability measure on C^n whose image carries an essentially free affine action, the affine group is amenable, which is absurd; every conjugacy onto (F_p^2)^Z dies for every p, including p = 2"
distinct_from:
  brin-thompson-2v-is-not-a-t-menable: that is the flagship refutation target; this kills one class of certificates for it (char-p lamp realizations with an invariant measure) and does not decide it.
  co-amenable-subgroups-transfer-hyperfinite-orbit-relations: that moves hyperfiniteness up from a co-amenable subgroup to an overgroup on the same space; this moves amenability down through a measure-preserving factor map to a different space and group.
  kazhdan-subgroups-of-nv-finite-iff-invariant-sets-carry-measures: that concerns Kazhdan subgroups of nV and their minimal sets; here the subgroup is arbitrary and the contradiction comes from the amenable tail relation, not from property (T).
---

**ESTABLISHED** by `char-p-lamp-realizations-with-invariant-measures-die-proof`.
- Imported verbatim: the Connes–Feldman–Weiss theorem in the form quoted from Elek–Timár
  (arXiv:2408.12565) in `co-amenable-hyperfinite-transfer-proof`.
- Imported from the graph: `elementary-linear-semidir-pair-relative-t` (ESTABLISHED). It is used
  only to show that `EL_2(F_p[t,t^-1])` is nonamenable.
- Everything else is proved in the route: Reiter functions for the tail relation, the transfer
  through a factor map, and freeness on Haar measure.
- Lane proof by swarm-0917-w17-w17-nv-pull. Not independently reviewed. No priority claimed: the
  measure-theoretic steps are standard (Zimmer).

## Setting

This is the setting of the char-p Burger lamp criterion (Theorem R) and of the injective class-kill
(Theorem K). Both are recorded in the nv-break lane as `char-p-burger-lamp-realizations-refute-haagerup`
and `injective-char-p-lamp-realizations-miss-fixed-points`. Only the following is used.

- **Spaces.** `p` is prime, `R = F_p[t,t^-1]` and `M = R^2`. `M^ = Hom(M, F_p) ≅ (F_p^2)^Z` is a
  compact abelian group with Haar probability `μ_H`.
- **Actions on `M^`.** `GL_2(R)` acts on `M^` by `γ·χ = χ∘γ^-1`. An affine map is
  `ξ ↦ γ·ξ + v`.
- **Realization.** `φ : C^n → M^` is continuous, where `C = {0,1}^N`, and `Λ ≤ nV`.
  `q : Λ → Aff(M^)` is a homomorphism with `φ∘λ = q(λ)∘φ`. The linear part of `q(Λ)`
  contains `EL_2(R)`.
  - When `φ` is affinely spanning, `q(λ)` is determined by `λ`. So `q` is automatically a
    homomorphism.

## Theorem H

**(a) General form.** Suppose there is a `Λ`-invariant Borel probability `ν` on `C^n` such that
`A = q(Λ)` acts essentially freely on `(M^, φ_*ν)`, meaning `φ_*ν(Fix a) = 0` for every
`a ≠ 1` in `A`. Then `A` is amenable. This is impossible, since `A` surjects onto a group
containing `EL_2(R)`. **So no such realization exists.**

**(b) Haar is free.** Every `a ≠ 1` in `A` has `μ_H(Fix a) = 0`. So (a) applies whenever
`φ_*ν = μ_H`.

**(c) Conjugacies die for every `p`.** If `φ` is a homeomorphism onto `M^`, take
`ν = (φ^-1)_* μ_H`. This measure is `Λ`-invariant. So no conjugacy of a subgroup of `nV` onto an
affine action on `(F_p^2)^Z` with linear part containing `EL_2(R)` exists, for any `n` and any `p`.
- For `p ≥ 3` this was already Theorem K(i).
- For `p = 2` it is new. Theorem K(iii) had left open conjugacies whose torsion lifts are all
  fixed-point free.
- In particular, **Proposition B's homeomorphism** (`p = 2`, `k = 2`, `φ∘B^2 = h∘φ`) cannot carry
  lifts of `e_12(1)`, `e_12(t)` and `w`, however the translations are chosen. So the lifting problem
  "for the same `φ`" is dead for this `φ`.

**(d) Measure-preserving lazy encodings die.** Let `β` be the uniform Bernoulli measure on `C^n`.
Suppose every generator of `Λ` preserves `β`. For example, a table element whose domain and range
bricks have equal total depth, such as the baker map `B`. Then any `φ` with `φ_*β = μ_H` dies. Here
`φ` need not be injective.

## Invariant and death step

- **Invariant.** The orbit relation of every subgroup of `nV` lies inside the product tail relation
  `E` on `C^n`, where coordinates are tail-equivalent with lag. `E` is Borel amenable, with explicit
  Reiter functions. So it is hyperfinite for every measure (Connes–Feldman–Weiss).
- **Death step, the same for every member.**
  - A `Λ`-invariant `ν` makes `φ` a measure-preserving factor map.
  - Averaging Reiter functions over the fibres of `φ` pushes amenability of the orbit relation down
    to the `A`-orbits on `(M^, φ_*ν)`.
  - Essential freeness then turns these into Reiter functions on the group `A`.
  - But `A` surjects onto a group containing `EL_2(R)`, which is nonamenable by relative (T).

## What survives

Any realization that still refutes Haagerup must satisfy the following.
- **(S1)** `Λ` preserves **no** probability measure on `C^n` whose image carries an essentially free
  `A`-action. In particular:
  - it preserves no lift of Haar measure;
  - if `φ` is surjective, the lifts cannot all be `β`-preserving with `φ_*β = μ_H`.
- **(S2)** So the lifts must jointly distort measure. Individual lifts may preserve `β`, as the
  torus lift `B^k` does, but the lifting subgroup as a whole cannot preserve any measure of this
  kind.
- Surjective non-injective `φ` without an invariant lift are untouched. So are injective `φ` whose
  image `Y` carries no `A`-invariant measure that is free on `Y`. Factors of amenable relations need
  not be amenable without an invariant measure; the example is boundary actions of free groups.
