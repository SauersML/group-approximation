---
rg: 2
id: full-mf-radical-finite-challenge-cylinder
kind: claim
title: A finite presentation and one surviving word certify a clopen family with full MF radical
root: true
distinct_from:
  clopen-non-mf-cylinder: that claim uses the manuscript's literal eight-generator central-sign presentation and concludes only non-MF; this claim uses the torsion-free two-generated saturation output and every group in its cylinder has the stronger full-MF-radical property.
  defect-saturation-full-mf-radical: that claim constructs one group and proves quotient heredity abstractly; this one packages finite presentation plus one inequation as a local certificate for an entire clopen family of marked quotients.
  continuum-nonisomorphic-non-mf-cylinder: that open claim asks for continuum many abstract isomorphism types inside a particular eight-marked cylinder; this claim asserts nonemptiness and full radical in a different two-marked cylinder and makes no multiplicity assertion.
artifacts:
  - research/artifacts/hyperlinear-to-mf-saturation-compiler-2026-08-22.md
  - research/artifacts/shadow-kleene-saturation-compiler-2026-08-22.md
  - notes/TORSION_FREE_SATURATION_DIRECT_ROUTE_2026-08-14.md
  - GroupApproximation/Sofic/TorsionFreeFullMFRadical.lean
---

Let the 2-generated finitely presented group from
`defect-saturation-full-mf-radical` be

```text
Q = <x_1,x_2 | R>,
```

and choose a word `v` nontrivial in `Q`.  The two-marked groups satisfying
all relations in the finite set `R` and the single challenge `v != 1` form a
nonempty clopen cylinder.  Every group in this cylinder satisfies

```text
normMFResidual L = top
```

and is non-MF.

Thus `(R ; v != 1)` is a finite verifier certificate for full MF failure.
Additional quotient relations either kill `v` or leave the quotient inside
the same full-radical class.
