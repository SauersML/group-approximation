---
rg: 2
id: inverse-semigroup-bcs-globalization-no-go-proof
kind: route
title: Use commuting idempotents, then audit fixed-point trace after globalization
target: inverse-semigroup-globalization-cannot-groupify-nonru-bcs
requires:
  - full-group-subgroup-trace-generation-dichotomy
  - mipstar-bcs-tracial-nonru-exists
---

In every inverse semigroup the idempotents form a commutative semilattice.  If
`v^*v=q_(c,a)` or `vv^*=q_(c,a)`, each context atom is such an idempotent.
Thus all atoms commute, and the shared-variable sum formulas make all binary
spectral projections commute.  Their finite-dimensional joint spectrum is
nonempty because they generate a unital algebra.  The BCS polynomial
relations vanish in that algebra, hence vanish at every character, producing
a classical solution.  This contradicts the absence of an `R^U` model and
proves the local no-go.

A group has only one idempotent, proving collapse under any inverse-semigroup
homomorphism to a group.  For a relation groupoid, bisection supports lie in
the Cartan and the same commuting-idempotent proof applies.  Finally,
`tau(u_g)=mu(Fix(g))` is the standard Feldman--Moore trace formula.
`full-group-subgroup-trace-generation-dichotomy` handles its two cases:
positive fixed-point mass violates the regular trace, while essential
freeness makes the generated group algebra intersect the Cartan only in the
scalars.  This proves the canonical-trace and isotropy assertions.

