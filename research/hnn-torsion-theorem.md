---
rg: 2
id: hnn-torsion-theorem
kind: claim
title: HNN extensions of torsion-free groups are torsion-free
distinct_from:
  torsion-free-higman-embedding: that is the Higman-style EMBEDDING statement — every recursively presented torsion-free group sits inside a finitely presented torsion-free one; this is the torsion-freeness PERMANENCE lemma for a single HNN extension over a torsion-free base, one step of the machinery such an embedding would iterate, and neither statement implies the other.
  concrete-compression-source: That claim constructs the compression source datum (compression relation, centralized witness, Britton nontriviality); this one is the torsion-freeness of the same skeleton, the recorded missing step for a fully torsion-free certified source.
artifacts:
  - GroupApproximation/Algebra/HNNTorsionFree.lean
---

OPEN (reduced to one lemma).  If the base of an HNN extension is
torsion-free in the power sense, so is the whole extension; classically
every finite-order element is conjugate into the base (Lyndon--Schupp
IV.2).  For the routing program this is the single recorded step
between `ConcreteCompressionSource.integerSource` and a fully
torsion-free certified compression source.

Machine-checked today (`GroupApproximation/Algebra/HNNTorsionFree.lean`):

- the **Britton power theorem** — a cyclically reduced word with at
  least one stable letter has infinite order
  (`CyclicWord.elem_pow_ne_one`): powers of a head-absorbed cyclic word
  are literal concatenations of its letter list, the seam condition
  keeps each concatenation Britton-reduced, and Mathlib's Britton lemma
  refuses a nonempty reduced word in the base copy;
- the **reduction** (`isPowerTorsionFree_of_existsCyclicConjugate`):
  cyclic-reduction existence plus a torsion-free base yields a
  torsion-free extension, with the base-conjugate case handled by
  injectivity of the base copy;
- the **stable-letter grading** (`lengthHom`,
  `pow_ne_one_of_lengthHom_ne_one`, `t_pow_ne_one`): every element with
  a nonzero net stable-letter count has infinite order, so all torsion
  lives in the grading kernel;
- the **skeleton corollaries**
  (`isPowerTorsionFree_sourceGroup_of_existsCyclicConjugate`,
  `isPowerTorsionFree_integerSourceGroup_of_existsCyclicConjugate`):
  the affine source and the explicit integer instance are torsion-free
  conditional on exactly [[hnn-cyclic-reduction-lemma]], the base side
  being already certified.

What remains is only [[hnn-cyclic-reduction-lemma]].

## Attempts

The 2026-08-15 session (route
[[hnn-torsion-theorem-proof]]) proved everything except
cyclic-reduction existence, which is where the obvious attack dies
today: it needs both an every-element-spelled-by-a-reduced-word
statement (the built Mathlib environment exposes
`ReducedWord.exists_normalWord_prod_eq` for words already given, but no
existence-from-an-element statement — it would have to be extracted
from the `NormalWord` action machinery) and the conjugation-shortening
induction on stable-letter length, whose pinch step rewrites through
`HNNExtension.equiv_eq_conj` with product bookkeeping on `ReducedWord`
that the current API does not assist.  Both are elementary but
genuinely new formal combinatorics; deferred, no obstruction
identified.
