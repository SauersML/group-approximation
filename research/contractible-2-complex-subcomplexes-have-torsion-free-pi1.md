---
rg: 2
id: contractible-2-complex-subcomplexes-have-torsion-free-pi1
kind: claim
title: Every finite connected subcomplex of a contractible 2-complex has torsion-free fundamental group
distinct_from:
  whitehead-asphericity-conjecture: that asserts asphericity, hence cohomological dimension at most 2, for every subcomplex of an aspherical 2-complex; this asks only for torsion-freeness, and only for finite subcomplexes of contractible complexes, and follows from it through `whitehead-conjecture-gives-torsion-free-subcomplex-pi1`.
  nonaspherical-subcomplex-of-contractible-2-complex-exists: that is the existence of a non-aspherical subcomplex; a finite subcomplex with torsion in its fundamental group would be one, so refuting this claim establishes that one.
  subcomplex-pi1-kernels-vanish-in-hyperlinear-quotients: that is an unconditional constraint on hyperlinear quotients of these fundamental groups; it does not exclude torsion.
  spine-epsilon-images-avoid-contractible-2-complexes: that is the special case needed for small-fiber images of the Poincaré spine; this is the general statement that implies it.
artifacts:
  - research/artifacts/eilenberg-ganea-frontier-2026-09-16.md
---

**OPEN.** Let `Y` be a contractible 2-dimensional CW complex and `K ⊆ Y` a finite connected
subcomplex. Then `π_1(K)` is torsion-free.

## Position

- **Implied by Whitehead.** `whitehead-asphericity-conjecture` implies this claim, through
  `whitehead-conjecture-gives-torsion-free-subcomplex-pi1`: aspherical finite 2-complexes have
  torsion-free fundamental groups.
- **Refutes Eilenberg--Ganea.** This claim implies
  `spine-epsilon-images-avoid-contractible-2-complexes`, through
  `contractible-2-complex-torsion-free-gives-spine-images-avoid`: a small-fiber image of the
  Poincaré spine contains `SL(2,5)` in its fundamental group. That claim in turn gives geometric
  dimension 3 for the Bestvina--Brady kernel.
- **Refuting it refutes Whitehead.** A torsion element gives infinite cohomological dimension, so
  `K` would be non-aspherical.
- **Relation to Gersten.** For finite subcomplexes of aspherical 2-complexes, asphericity is
  equivalent to `cd π_1(K) ≤ 2` (Gersten, arXiv:1501.06875; abstract only). This claim asks for the
  weaker conclusion that there is no torsion.

## Attempts

1. **Hyperlinear quotients.**
   - Let `c ∈ π_1(K)` be a torsion element detected by a homomorphism `ρ` to a finite group.
     `subcomplex-pi1-kernels-vanish-in-hyperlinear-quotients`(a) forbids `c` from dying in any
     finite enlargement `Z ⊇ K` of `Y` with `H_1(K) → H_1(Z)` injective.
   - `c` does die in `Y`. So every null-homotopy of `c` must complete a relative cycle of
     `H_2(Y, K)`.
   - No argument was found that some null-homotopy avoids this, so there is no contradiction.
   - Where `ρ` does not exist (non-residually-finite `π_1(K)`), nothing at all is obtained.
2. **Acyclic subcomplexes.**
   - When `H_1(K) = 0`, part (b) of the same claim removes all finite and hyperlinear quotients.
   - That still does not exclude torsion, because a group with no nontrivial hyperlinear quotient
     can contain torsion a priori.
3. **Homology.**
   - `H_1(K)` is free and `H_2(K) = 0`. Torsion in `π_1(K)` is invisible to both.
   - For a finite cyclic subgroup `C`, the covering `K_C` has `π_1 = C`, so its universal cover is
     not contractible. But no homological constraint on `K_C` coming from `Y` was found.
   - Dies.

No source among those in the artifact, §1, settles this claim. Its status against the survey
literature on Whitehead's question was not checked.
