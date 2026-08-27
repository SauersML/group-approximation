---
rg: 2
id: contextual-fano-cap-compiler-is-equivalent-to-perfect-lcs
kind: claim
title: A contextual Fano-cap compiler is equivalent to a perfect-completeness LCS compiler
distinct_from:
  culf-mastel-rstar-uniform-fano-cap-profile: that asks for the direction from a cap-supported R-star family to LCS for the specific Culf--Mastel source; this proves the converse compiler reduction and allows arbitrary finite contextual quantum auxiliaries.
  fano-cap-range-sections-cannot-encode-nonaffine-relations: that forbids a classical pp section covering every assignment of one nonaffine source relation; this permits a model-dependent contextual perfect representation and identifies its exact computational strength.
  rstar-cap-support-is-one-character-row: that is the local representation equivalence for one R-star instance; this is the uniform two-way reduction between whole perfect-gap compiler tasks.
---

**ESTABLISHED COMPILER EQUIVALENCE.**  Consider effective machine-indexed
finite compilers with the orientation

```text
HALT:    a perfect commuting/tracial marked model exists,
NONHALT: no perfect tracial matrix-ultraproduct marked model exists.      (CFC1)
```

The following two compiler tasks are equivalent under effective finite
reductions preserving `(CFC1)`.

1. Output a finite binary LCS.
2. Output a finite `R_*` constraint system in the standard relational syntax
   permitting repeated scope entries, with arbitrary finite contextual
   quantum auxiliary variables and shared-variable geometry, for which the
   HALT model may be chosen with Fano-cap support at every `R_*` context.

For `2 -> 1`, cap support is exactly one of seven character rows per context.
Enumerate the finite profile menu and apply the exact product-sign LCS OR.

For `1 -> 2`, first ternarize every LCS equation with partial-sum variables.
Retain every original pairwise commutation requirement by placing every pair
from an original equation in an auxiliary `R_*` context.  Use a finite
cap-supported `R_*` pinning gadget to obtain bits `c_0=0,c_1=1`.  Encode a
ternary equation by

```text
x+y+z=1    <=> R_*(c_0,x,y,z),                       (CFC2)
x+y+z=0    <=> R_*(x,c_1,y,z).                       (CFC3)
```

The first row is the maximal cap `x_2+x_3+x_4=1`; the second is the maximal
cap `x_2=1`.  Every pairwise commutation row has a cap-supported extension by
the fixed two-coordinate section theorem.  Thus every perfect LCS model
extends to a cap-supported perfect `R_*` model.  Conversely every exact
`R_*` model decodes the ternary parity chain and all original commutations,
so it gives an exact model of the source LCS.

Therefore allowing a genuinely contextual quantum gadget does evade the
*classical pp-section proof* but does not weaken the missing theorem.  A
uniform gadget that solves the Culf--Mastel Fano-support gate is already a
perfect-completeness LCS compiler; conversely such an LCS compiler already
supplies a contextual cap-supported `R_*` gadget.  Contextuality can be the
construction method, but it cannot be an intermediate target strictly below
perfect LCS completeness.

If a chosen CSP formalism requires four distinct variables in every scope,
the forward implication `2 -> 1` is unchanged.  The converse then additionally
requires a cap-supported implementation of repeated-coordinate equality; that
syntax conversion is not silently asserted here.
