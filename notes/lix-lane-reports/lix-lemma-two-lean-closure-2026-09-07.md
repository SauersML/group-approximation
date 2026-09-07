# Lemma 2 closes: hres, hclass, hsq, and an unconditional `not_problemLIX` (2026-09-07)

Cross-lane campaign summary, not a per-lane report (`README.md`'s four-section
schema is per-lane; this is written by `lix-meta` to record the closing wave
across `lix-hres`, `lix-hclass`, `lix-hsq` and `cs-endpoint`/wiring). Every
declaration name, file, and commit hash below was read directly out of
`git show`/`git cat-file -e origin/main:<path>` while writing this file, not
relayed from another lane's report.

## What closed

`GroupApproximation/CharClass/LIXStepCOddWired.lean`'s
`lix_topClass_ne_zero_of_three` -- Step C's odd side, over three open
hypotheses `hsq`, `hres`, `hclass` -- is the seam `notes/LIX_FULL_PROGRAM_2026-09-05.md`
§1.4 identified as the topological core still owed. Three lanes closed the
three hypotheses independently, one at a time, each verified before landing
to the same standard (below):

| hypothesis | declaration | file | commit |
|---|---|---|---|
| `hres` | `GroupApproximation.CharClass.injective_lixRes` | `CharClass/LIXResFibre.lean` | `59796080e` |
| `hclass` | `GroupApproximation.CharClass.lixHclass` | `CharClass/LIXHclass.lean` | `1a75df323` |
| `hsq` | `GroupApproximation.CharClass.lixHsq` | `CharClass/LIXHsq.lean` | `ef0b678cb` |

`hsq`'s binder-level check -- that `lixHsq`'s statement has not drifted from
what `lix_topClass_ne_zero_of_thom` actually consumes, the one thing no
single-lane probe can see because a lane never mentions its consumer -- is a
separate declaration, `lix_topClass_ne_zero_of_hsq` in
`CharClass/LIXStepCOddHsq.lean`, commit `db39e594e`.

`CharClass/LemmaTwoOfHsqHresHclass.lean`, commit `1c3237f2c`, threads all
three into `lix_topClass_ne_zero_of_three` and `LemmaTwoOddNonvanishing.lean`'s
`lemmaTwoHolds_of_oddNonvanishing`, producing, with **zero hypotheses**:

```lean
theorem GroupApproximation.CharClass.lemmaTwoHolds : LIX.LemmaTwoHolds
theorem GroupApproximation.CharClass.not_problemLIX : ¬ NinetyNineProblems.ProblemLIX
```

`not_problemLIX` here is the negation of exactly STW Problem LIX as stated in
`Manuscript/NinetyNineProblems/ProblemLIX.lean`
(`∀ (A : Type) [CStarAlgebra A], Nontrivial A → IsSimpleCStar A → K1Inj A`).
It is kept at `#audit_axioms` rather than `#audit_closed_axioms` in this file
deliberately (documented in the file's own module docstring: the closed gate
would in fact accept it on syntactic grounds, but the one point of
`#audit_closed_axioms` certification for this result is reserved for the
reader-facing wrapper in `ProblemLIX.lean` itself) -- **not** because anything
is still conditional. Full research-graph record of the claim and its proof
chain: `research/stw59-lean-witness-simple-unital-not-k1-injective.md` and
`research/stw59-lean-witness-simple-unital-not-k1-injective-proof.md`.

## Wiring

Both the composition file and the thirteen modules carrying the three
residues are imported by the repository root
(`GroupApproximation.lean:3888`, `:3965-3975`), landed in two root-wiring
commits:

* `6785a5dd2` -- ten modules (the `hres`/`hclass` closure plus four of
  `hsq`'s support modules).
* `bc9632ea0` -- the last three (`LIXHsqLegs`, `LIXHsq`, `LIXStepCOddHsq`).

## The verification standard used throughout

Every landing above was checked, before push, against the same four
criteria (recorded per-landing in `notes/lix-lane-reports/cs-endpoint.md` and
`notes/lix-lane-reports/cc-thom.md`'s probe logs):

1. **A clean-export build.** `lake build GroupApproximation` against the
   shared working tree compiles whatever every lane happens to have on disk
   at that moment, including mid-authorship drafts; a `git archive` export of
   `origin/main` (with, for a pre-landing check, only the one change applied)
   builds exactly the committed bytes and nothing else.
2. **A genuine build, not a replay.** The log must show `Built <module>`
   lines for the new/changed modules, not `Replayed <module>` -- Lake will
   happily report success while reusing a stale `.olean` from an earlier,
   possibly-broken state.
3. **`sorryAx: none`**, checked against a build whose axiom-line count is
   itself nonzero (a run that emitted no axiom lines would report the same
   clean result having checked nothing).
4. **Axiom lines read by declaration name.** `#print axioms <decl>` output
   for the specific new theorems, by name, off the raw log -- not a summary,
   not a grep count. Every one seen in this closure reports exactly
   `[propext, Classical.choice, Quot.sound]`.

Two root-wiring commits report the full-root form of this standard directly
in their own commit messages: `6785a5dd2` -- `Build completed successfully
(13819 jobs)`, `LAKE_EXIT=0`, `sorryAx: none` over 2921 `depends on axioms`
lines; `bc9632ea0` -- `Build completed successfully (13822 jobs)`,
`LAKE_EXIT=0`, `sorryAx: none` over 2929 `depends on axioms` lines. The
`hres`/`hclass`/`hsq` discharges were each additionally re-verified from
clean-export bytes on a separate clone by a forced fresh compile before being
cleared, per `cs-endpoint.md`.

## What is still open

The reader-facing wrapper `GroupApproximation.NinetyNineProblems.not_problemLIX`
in `Manuscript/NinetyNineProblems/ProblemLIX.lean`, intended to carry
`#audit_closed_axioms` for the STW-99-problems endpoint roster, was not yet
landed as of this writing -- `cs-endpoint.md` records it HELD pending a
from-clean-export fresh compile of `lixHsq`. This is bookkeeping, not open
mathematics: `CharClass.not_problemLIX` above already proves the same
statement with zero hypotheses, and the wrapper is a one-line application of
it under a different audit macro. Lane `lix-wire` owns landing it.

Also still open, and out of scope for the LIX answer itself (see
`notes/LIX_FULL_PROGRAM_2026-09-05.md` §0): `K1(A) = 0` for the counterexample
algebra, and the exact order of the witness unitary in `U(A)/U0(A)`. Neither
is computed anywhere in this chain.
