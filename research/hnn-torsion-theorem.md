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
  - GroupApproximation/GroupTheory/HNNBrittonCyclic.lean
---

ESTABLISHED and machine-checked.  If the base of an HNN extension is
torsion-free in the power sense, so is the whole extension; classically
every finite-order element is conjugate into the base (Lyndon--Schupp
IV.2).  For the routing program this is the single recorded step
between `ConcreteCompressionSource.integerSource` and a fully
torsion-free certified compression source.

The proof is split across `GroupApproximation/Algebra/HNNTorsionFree.lean`
and `GroupApproximation/GroupTheory/HNNBrittonCyclic.lean`:

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
- the **cyclic-reduction theorem** (`HNNBritton.existsCyclicConjugate`): every
  HNN element is conjugate into the base or to a cyclic word;
- the **unconditional endpoint** (`HNNBritton.isPowerTorsionFree_hnn`), with
  source corollaries `HNNBritton.isPowerTorsionFree_sourceGroup` and
  `HNNBritton.isPowerTorsionFree_integerSourceGroup`.

There is no remaining hypothesis.  The affine-congruence source consumes the
unconditional source corollary directly.

## Attempts

The earlier 2026-08-15 reduction stopped at cyclic-reduction existence.  That
residual was subsequently closed in [[hnn-cyclic-reduction-lemma-proof]] by
extracting normal words from Mathlib's action machinery and formalizing the
conjugation-shortening pinch induction.  The conditional declarations remain
useful as an abstract interface, but they are no longer on the trust surface.
