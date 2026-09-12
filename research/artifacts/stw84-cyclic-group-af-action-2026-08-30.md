# Audit: cyclic group-AF actions

Date: 2026-08-30

## What is proved

For every automorphism of every countable locally finite group, the
semidirect-product group algebra is AF-embeddable.  The proof uses only the
faithful regular trace, amenability, and Brown's equivalence for AF
coefficients.

The augmentation character is invariant under every group automorphism and
gives the exact sequence

```text
0 -> I_K rtimes Z -> C*(K rtimes Z) -> C(T) -> 0.
```

Therefore only the augmentation-ideal crossed product remains to be bounded;
a bound `d` there gives `d+2` for the full group algebra.

## Rokhlin-dimension firewall

The augmentation quotient carries the trivial integer action.  Ordinary
Rokhlin dimension passes to quotients, while transitivity and order-zero
orthogonality force every equivariant cyclic tower map into the trivial
scalar action to vanish.  Hence ordinary Rokhlin dimension is infinite for
every action in the cyclic group-origin family.  This does not address
relative or idealwise tower notions after augmentation has been removed.

## Alternating-shift checks

For a finite set of finitary alternating permutations, translation on their
common finite support extends to conjugation by one finitary permutation.
Parity is corrected on two fresh points.  The induced AF-algebra
automorphism is therefore approximately inner.

The translates of `(0,1,2)` are the adjacent three-cycles, which generate
the finitary alternating group.  Thus one finite seed has infinite orbit
hull, so the action has no invariant finite-subgroup exhaustion despite its
approximate innerness.

## Boundary

AF-embeddability and quasidiagonality do not imply finite nuclear dimension
for a nonsimple algebra.  Approximate innerness likewise supplies no known
uniform nuclear-dimension estimate here.  The package deliberately leaves
`I_K rtimes Z` as the exact positive-rank hinge and makes no finite-dimension
claim for it.
