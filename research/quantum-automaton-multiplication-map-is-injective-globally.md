---
rg: 2
id: quantum-automaton-multiplication-map-is-injective-globally
kind: claim
title: For a quantum automaton the multiplication map from the image tensor the relative commutant to the quasi-local algebra is injective
distinct_from:
  quantum-endomorphisms-split-off-their-relative-commutant: that is the full splitting statement with the local defect criterion and the index dichotomy; this is only the missing Step 4 of its drafted route, the passage from injectivity on each local piece to injectivity on the global tensor product.
  projection-comparison-lifts-through-injective-limits: that lifts projection comparisons through injective inductive limits; this is injectivity of one multiplication map on a minimal tensor product built from an inductive limit.
---

**OPEN** (gap node opened by the 2026-09-17 audit of `quantum-endomorphisms-split-off-their-relative-commutant`).

**Setting.** As in `quantum-endomorphisms-split-off-their-relative-commutant`: `A = (x)_G M_d`, `Phi` a unital
shift-equivariant *-endomorphism with `Phi(A_e) <= A_N` for a finite `N`, and `D = Phi(A)' n A`.

**Statement.** The multiplication map `Phi(A) (.) D -> A`, `a (x) x |-> a x`, extends to an injective
*-homomorphism `Phi(A) (x)_min D -> A`.

**What is known.** For each finite `L`, multiplication `Phi(A_L) (x) (Phi(A_L)' n A) -> A` is a *-isomorphism
(matrix slicing, Step 0 of the drafted route), so it is injective on `Phi(A_L) (.) D`. The referee's suggested
completion: the local maps are isometric for the min norm and extend isometrically to `Phi(A) (x)_min D`, and the
multiplication map agrees with this extension by continuity; equivalently, an ideal of an inductive limit is the
closure of its intersections with the finite stages.

## Attempts

1. **Local injectivity plus inductive limit (2026-09-17, drafted Step 4 of
   `quantum-endomorphisms-split-off-their-relative-commutant-proof`).** Injectivity on each `Phi(A_L) (.) D` was
   asserted to pass to `Phi(A) (.) D` because `Phi(A)` is the inductive limit of the `Phi(A_L)`. Where it dies:
   elements of the algebraic tensor product use non-local `a_i`, so the passage needs the min-norm isometry and
   continuity argument above, which was not written. The attack is deferred to whoever restores the parent route.
