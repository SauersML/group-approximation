---
rg: 2
id: amenable-implies-operator-mf
kind: claim
title: Countable amenable groups are operator MF
distinct_from:
  lef-implies-operator-mf: that is the elementary sufficient condition, proved in-repo through exact finite models; this is the strictly larger amenable class, which those models provably cannot reach.
  permutation-norm-models-certify-exactly-lef: that is the established limitation theorem saying the Folner construction reaches exactly LEF; this is the statement the limitation theorem says needs a different input.
  mf-positive-controls: that records the in-repo positive controls (subgroups, residually finite, locally finite); this is the one positive control the repository does not have.
artifacts:
  - non_mf_groups_exist.tex
  - GroupApproximation/Analysis/AmenableQuasidiagonal.lean
  - GroupApproximation/Algebra/AmenableMFProof.lean
---

ESTABLISHED by citation (`amenable-implies-operator-mf-citation`); not
formalized.  Every countable amenable group is operator MF.

This is a **published theorem, not a conjecture**: it is the standard
consequence of quasidiagonality of the reduced group C-star algebra of an
amenable group, which the manuscript attributes to Tikuisis--White--Winter and
invokes as "and, by quasidiagonality, all amenable groups" (introduction) and
"is therefore amenable, hence MF by [TWW]" (*Sharpness of the Kazhdan
hypothesis*).  It is flagged as unformalized for one reason only: it is
not formalized, nothing in `GroupApproximation/` proves it, and no hypothesis
anywhere in the development stands in for it.

## Why it cannot be quietly assumed

[[permutation-norm-models-certify-exactly-lef]] is the established measure of
the gap.  Every positive MF result in the repository —
`isOperatorMF_of_residuallyFinite`, `isOperatorMF_of_isLEF`,
`isOperatorMF_of_locallyFinite` — factors through **exact** finite models, and
the Følner construction cannot escape that class: permutation operator-norm
models certify exactly the LEF groups, because the operator-norm defect of a
permutation model is `0` or at least `1` with nothing in between.  So this claim
is not "an easy step nobody bothered to write"; reaching it needs genuinely
non-permutation unitaries, which is the quasidiagonality input itself.

Reachable special cases, both machine-checked, are *not* substitutes: countable
locally finite groups are amenable and MF
(`isAmenable_and_isOperatorMF_of_isLocallyFiniteGroup`), and so are residually
finite amenable groups.  Both go through LEF.  No amenable group outside the LEF
class is certified MF anywhere in this repository.

## What depends on it

[[cyclic-base-sharpness]], through its detector: the Clifford quotient of the
literal cyclic-base analogue is amenable but is *neither residually finite nor
LEF*, so its MF-ness is exactly this input and nothing weaker.  That is also the
recorded difference between that claim and
[[commuting-lamp-quotient-mf]], where the same route is unavailable for a
different reason — the affine base has property (T), so the quotient is not
amenable at all.

## How to close it

Either formalize the analytic theorem, or — the cheaper and equally legitimate
move under this project's conventions — write an
`amenable-implies-operator-mf-citation` route in the house style for literature
imports, recording the source actually read and the exact statement quoted, and
add it to the `LITERATURE_INPUT` roster in `scripts/Audit.lean` so the audit
gate keeps the trust surface visible.  This node deliberately does **not**
carry such a route, because no source was read for it in the session that
created the node.
