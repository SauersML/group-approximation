---
rg: 2
id: stw59-lean-witness-simple-unital-not-k1-injective-proof
kind: route
title: Three residues (hres, hclass, hsq) close Step C's odd side, and the wired composition proves not_problemLIX in Lean
target: stw59-lean-witness-simple-unital-not-k1-injective
requires: []
artifacts:
  - notes/lix-lane-reports/lix-lemma-two-lean-closure-2026-09-07.md
  - notes/lix-lane-reports/cc-thom.md
  - notes/lix-lane-reports/cs-endpoint.md
---

Direct proof, entirely in Lean 4 over Mathlib plus this repository's
`GroupApproximation` development; no open hypothesis anywhere in the chain
below. Every declaration and commit named here was read out of
`git show`/`git cat-file -e` against `origin/main`, not relayed from a lane
report.

## The chain

`GroupApproximation/CharClass/LIXStepCOddThom.lean`'s
`lix_topClass_ne_zero_of_thom` is Step C's odd side (the manuscript's
transverse-zero-of-a-section argument, over the vendored mod-2
singular-cohomology tree), stated with eleven open binders.
`LIXStepCOddRelative.lean` supplies eight of them unconditionally (the
relative-cohomology exact-sequence data). The remaining three --
`hsq` (the model/restriction compatibility square), `hres` (injectivity of
the fibre restriction) and `hclass` (the Thom class pulls back to the
mapping-torus's top class) -- were the open residues this campaign closed:

* `hres` -- **`GroupApproximation.CharClass.injective_lixRes`**,
  `GroupApproximation/CharClass/LIXResFibre.lean`, commit `59796080e`
  ("LIX lix-hres: hres, by the fibre over the zero and not by the ball").
* `hclass` -- **`GroupApproximation.CharClass.lixHclass`**,
  `GroupApproximation/CharClass/LIXHclass.lean`, commit `1a75df323`
  ("lix: hclass discharged -- the Thom class restricts to the top Chern
  class").
* `hsq` -- **`GroupApproximation.CharClass.lixHsq`**,
  `GroupApproximation/CharClass/LIXHsq.lean`, commit `ef0b678cb` ("LIX
  lix-hsq: hsq, the compatibility square of Step C's odd side"); the
  binder-level check that `lixHsq`'s statement has not drifted from what
  `lix_topClass_ne_zero_of_thom` actually consumes is a separate declaration,
  `lix_topClass_ne_zero_of_hsq` in `LIXStepCOddHsq.lean`, commit `db39e594e`.

`GroupApproximation/CharClass/LIXStepCOddWired.lean`'s
`lix_topClass_ne_zero_of_three` plugs the eight relative terms into
`lix_topClass_ne_zero_of_thom` in place, leaving exactly `hsq`, `hres`,
`hclass` as its own three arguments.
`GroupApproximation/CharClass/LemmaTwoOfHsqHresHclass.lean`, commit
`1c3237f2c` ("CharClass: hsq discharged -- Lemma 2 and not-Problem-LIX are
unconditional"), instantiates all three from the theorems above (no
adjustment for `hsq` and `hres`; two pinned proof arguments for `hclass`),
proving:

```lean
theorem lemmaTwoHolds : LIX.LemmaTwoHolds
theorem not_problemLIX : ¬ NinetyNineProblems.ProblemLIX
```

both in `namespace GroupApproximation.CharClass`, both with **zero
hypotheses**. `not_problemLIX` follows via
`NinetyNineProblems.not_problemLIX_of_lemmaTwo`
(`Manuscript/NinetyNineProblems/ProblemLIX.lean`), which unwinds through
`LIX.lixLimit_hasK1InjWitness_of` (Corollary 4 plus the generalized clutching
argument, `Analysis/LIXLemmaSixCor4.lean`), `LIX.lixLimit_isSimpleCStar`
(stagewise fullness, `Analysis/LIXLimitSimple.lean`,
`#audit_closed_axioms`-clean) and `not_k1Inj_of_hasWitness`
(`Analysis/LIXEndpointStatement.lean`) to the witness claimed by the target
node. `ProblemLIX` itself is
`∀ (A : Type) [CStarAlgebra A], Nontrivial A → IsSimpleCStar A → K1Inj A`
(`Manuscript/NinetyNineProblems/ProblemLIX.lean`), so `not_problemLIX`'s type
is exactly the negation of STW's printed problem.

## Wiring and build verification

Both `LemmaTwoOfHsqHresHclass.lean` and the thirteen modules carrying the
three residues (`LIXResFibre`, `ThomChartSquare`, `ThomJmNatural`,
`LIXHclass`, `ThomBridgeRelToAbs`, `ThomChartTautZero`,
`LIXHsqNeighbourhood`, `LIXHsqEta`, `LIXHsqLinear`, `LIXHsqHomotopy`,
`LIXHsqLegs`, `LIXHsq`, `LIXStepCOddHsq`) are imported by the repository
root, `GroupApproximation.lean` (line 3888 for the composition file; lines
3965-3975 for the residue modules), so they are compiled by an ordinary root
build, not merely reachable from a private clone.

Two root-wiring commits report full clean-export builds directly in their own
commit messages (read via `git show -s --format=%B`, not paraphrased):

* `6785a5dd2` -- root build from a clean `git archive` export of
  `origin/main`: `Build completed successfully (13819 jobs)`, `LAKE_EXIT=0`,
  `sorryAx: none` over 2921 `depends on axioms` lines.
* `bc9632ea0` -- same standard after wiring the final three modules:
  `Build completed successfully (13822 jobs)`, `LAKE_EXIT=0`, `sorryAx: none`
  over 2929 `depends on axioms` lines.

`notes/lix-lane-reports/cs-endpoint.md`'s own landing log (2026-09-07)
records each of the three discharges verified before landing to the same
standard -- fresh compile (not a replay: `Built ...`, not `Replayed ...`,
lines for every new module), `sorryAx: none`, and the axiom lines for the
newly-closed declarations read by exact name off the raw log
(`[propext, Classical.choice, Quot.sound]` throughout, no custom or `sorry`
axiom at any stage) -- and records the final composition, `1c3237f2c`, as
independently re-verified from clean-export bytes on a separate clone by a
forced fresh compile.

## Scope, precisely

Nothing in this chain computes `K1(A)`, computes the order of the witness
unitary in `U(A)/U0(A)`, or asserts nuclearity or stable finiteness of `A`;
none of those is needed by `ProblemLIX`, and none is claimed by the target
node. The reader-facing wrapper `NinetyNineProblems.not_problemLIX`, intended
to carry the `#audit_closed_axioms` badge for the STW-99-problems roster, was
still unlanded as of this writing (lane `lix-wire`); the mathematics recorded
here does not depend on that wrapper, only on `CharClass.not_problemLIX`
above, which is unconditional today.
