---
rg: 2
id: private-neighbour-completion-changes-clifford-module
kind: claim
title: Completion variation precedes the affine Clifford coboundary system
distinct_from:
  clifford-phase-space-curvature-is-a-twisted-f2-cocycle: that gives a linear coboundary equation after K and the symplectic actor maps are fixed; this proves that varying private-neighbour completions changes precisely that input data and therefore is not governed by the same fixed linear system
  private-neighbour-density: that handles bad sets which are affine denominator cosets in Laurent root parameters; this identifies why the phase-space condition has not yet been shown to have that form
  finite-clifford-symplectic-section-obstruction: that is a global nonsplitting result for a fixed Clifford extension; this is a local parameterization firewall and makes no nonsplitting assertion for a prescribed finite actor table
---

In the private-neighbour approach to
`minimal-marked-graph-finite-window-phase-space-section`, changing the
completion vertices can change all three of the following:

1. the completed nondegenerate symplectic space `K`;
2. the extensions `S_g` of the tested partial permutations to `K`;
3. hence the coefficient action `K_S` and the coboundary matrix `delta_S`.

Even after equal-dimensional completions are identified by a Witt isometry
which fixes the tested lamp span, two extensions of the same tested partial
map differ by an element of its pointwise symplectic stabilizer.  Writing

```text
S'_g = Q_g S_g,
```

the multiplication requirements become

```text
Q_g (S_g Q_h S_g^(-1)) = Q_(gh),                     (CVC1)
```

inside those stabilizers.  In matrix coordinates the simultaneous demands

```text
(S'_g)^T J S'_g = J,
S'_g S'_h = S'_(gh)                                  (CVC2)
```

are quadratic equations in the completion/extension entries.  Only after a
solution `S'` of `(CVC1)-(CVC2)` has been chosen does
`clifford-phase-space-curvature-is-a-twisted-f2-cocycle` reduce lift repair
to the affine equation `delta_(S') r=a_(S')`.

Therefore the existing Laurent coset estimate in `private-neighbour-density`
does not by itself imply that the bad Clifford completions are a finite union
of affine denominator cosets.  The exact remaining private-neighbour lemma
is to choose the completions and simultaneous Witt extensions so that the
resulting restricted class

```text
[a_(S')] in H^2(table; K_(S'))
```

vanishes.  Once that is done, the lift gauges are obtained by finite linear
algebra.

## Conditional finite-presentation warning

If a finite actor window contained a complete finite presentation of the
Kun--Thom actor and `(CVC1)-(CVC2)` produced an exact finite symplectic actor
representation, then that representation would factor through a finite
quotient.  Combined with `finite-quotient-blindness`, the marked element
would lie in the image of the lattice; a lattice-fixed base lamp vector would
then also be fixed by the marked element, contradicting the marked
anticommutation edge.  This is only a conditional warning: finite
presentability of the full Kun--Thom actor in the required range has not been
established here, so it is not a refutation of the finite-window target.
