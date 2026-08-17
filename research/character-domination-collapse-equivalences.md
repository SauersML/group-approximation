---
rg: 2
id: character-domination-collapse-equivalences
kind: claim
title: Finite-action collapse is a single linear character-domination constant, and its failure forces dimension escape
distinct_from:
  finite-quotient-blindness: That is about what a finite quotient cannot see in the compression lane; this is a quantitative equivalence between vanishing of a character at a word and existence of one domination constant, stated for an arbitrary group.
artifacts:
  - GroupApproximation/Domination/PaperStatements.lean
  - GroupApproximation/Domination/Core.lean
  - GroupApproximation/Domination/Comparison.lean
  - GroupApproximation/Domination/FixedDimension.lean
  - GroupApproximation/Domination/Irreducible.lean
---

ESTABLISHED.  `Domination/PaperStatements` is the stable interface of the
domination/dimension-escape lane, for an arbitrary group `G`, a finite subset
`R` and a word `w`:

* `finiteActionCollapse_iff_linearPermutationDomination` -- qualitative
  collapse of every finite action is *equivalent* to a single linear
  permutation-character domination constant;
* `finiteDimensionalCollapse_iff_linearUnitaryDomination` -- the same for
  finite-dimensional unitary characters, with a dimension-independent
  constant;
* `permutationDomination_of_unitaryDomination` -- the exact comparison
  `C_perm ≤ C_fd`, in predicate form;
* `obstruction_requires_matrixDimensionEscape` and
  `obstruction_requires_irreducibleDegreeEscape` -- if every fixed dimension
  (resp. every bounded irreducible degree) is controlled but the global
  constant is not, then bad representations exist with dimensions (resp.
  degrees) tending to infinity.

## Why the escape statements are the useful half

They convert a failure of uniformity into a *structure*: any counterexample to
the global constant must be witnessed by a sequence escaping to infinite
dimension, which is a thing one can look for. The module's own credit note is
explicit that Cartesian and tensor powers, conjugate doubling, complete
reducibility, semialgebraic curve selection, truncated jets and Mal'cev
residual finiteness are classical inputs, and that Elek--Szabó are credited for
the sofic-to-hyperlinear embedding; the analytic curve-selection bridge that is
not yet formalized is kept visible as a hypothesis rather than assumed.
