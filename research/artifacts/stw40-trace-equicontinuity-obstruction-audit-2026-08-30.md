# STW XL trace-equicontinuity obstruction audit (2026-08-30)

## Result

An amenable action of a nonamenable group on a unital separable nuclear
C-star algebra cannot have a nonempty invariant compact equicontinuous
subsystem in its trace simplex.

This strictly strengthens the finite-orbit observation.  It excludes
compact rotations, profinite trace dynamics, and every other trace subsystem
whose acting homeomorphisms have compact closure.

## Proof checks

- Weak-star compact subsets of `T(A)` are compact metrizable because `A` is
  separable.
- Equicontinuity of a group of homeomorphisms includes equicontinuity of the
  inverses, since the inverse maps are indexed by the same group.
- Arzela--Ascoli makes the uniform closure compact.  Taking simultaneous
  limits of maps and inverses shows every limit remains invertible, so the
  closure is a compact topological group rather than merely a compact
  semigroup.
- Haar measure on that compact group pushes forward to an invariant
  probability measure on any orbit in `K`.
- Barycentering this measure gives an invariant tracial state on `A`.
- The previously established crossed-product/GNS argument then forces the
  acting group to be amenable, yielding the contradiction.

## Boundary

The theorem is an obstruction, not a construction for Problem XL.  It does
not assert positive entropy, strong proximality, or topological amenability
of the induced trace action.  It only proves that every nonempty invariant
compact part of the trace dynamics must fail equicontinuity.  Boundary
actions of exact nonamenable groups have exactly this qualitative shape,
which sharpens the target for a classifiable realization.
