# Build test of the 14 WIRE/NEEDS-PROBE orphan candidates — 2026-09-07

Lane `lix-wire`. Assignment: build-test, as explicit `lake build` targets (never via
the root), every module `notes/orphan-module-sweep-2026-09-07.md` classified WIRE,
plus the three KTheory NEEDS-PROBE modules. Do not wire, do not edit
`GroupApproximation.lean`.

## Method and provenance

All 14 targets probed in one `lixprobe8.sh cs-stages` call (`lake build` with all
fourteen as explicit targets — they do not import each other, confirmed already by
the sweep note, so batching is safe and each target's pass/fail is independently
legible in the log).

**Every one of the 14 target files' local content is byte-identical to
`origin/main` at `ca19a87d0`** (`diff <(git show origin/main:<path>) <path>` run on
all fourteen, individually, after this probe — zero differences). So this table is
a claim about `ca19a87d0`, not about an uncommitted local draft.

**Compiles yes/no** is read off `lake`'s own `Some required targets logged
failures:` list, not inferred from log-line presence — that list is `lake`'s
authoritative verdict per explicit target and is unaffected by any output
filtering.

**Sorry count** is `grep -c "declaration uses" <log>` **restricted to lines Lean
itself emitted** (`error: <path>:<line>:<col>: declaration uses `sorry`` —
promoted to `error:` here because this project builds under
`-DwarningAsError=true`), not a lexical scan of source text. Full command and
output reproduced below the table.

## Table

| Module | Compiles | Sorry (Lean) | First error (verbatim) |
|---|---|---|---|
| `Analysis.STW22FactorialCore` | **YES** | 0 | — |
| `Analysis.STW22TraciallyCompletePair` | **YES** | 0 | — (see note below: this is a change from the sweep report) |
| `Analysis.STW22AntipodalGaugeFactorial` | **YES** | 0 | — |
| `Analysis.STW22AntipodalFactorialPair` | **YES** | 0 | — |
| `Analysis.STW22CounterexampleCompactnessRoute` | **YES** | 0 | — |
| `Analysis.STW22FibreEvaluation` | **YES** | 0 | — |
| `GGT.DGOProposition414SecondSeparationHalfWord` | **YES** | 0 | — |
| `GGT.HullSCLemma44PrefixKernelCutConstruction` | **YES** | 0 | — |
| `GGT.KazhdanHypGirthEightGeodesicWord` | **NO** | 0 | `GroupApproximation/GGT/KazhdanHypGirthEightGeodesicWord.lean:115:6: Tactic \`rewrite\` failed: Did not find an occurrence of the pattern` `wordDist ?S ?x ?x` `in the target expression` `OsinComponents.IsGeodesicWord D x.val x.val word` |
| `GGT.KazhdanHypGirthEightGenericProducers` | **NO** | **2** (lines 84, 87) | `GroupApproximation/GGT/KazhdanHypGirthEightGenericProducers.lean:63:2: Type mismatch: After simplification, term` `C.after_power` `has type` `@Eq (List (RelLetter (FreeGroup Generator) PEmpty.{1})) C.replacement.diagram.boundaryWord (List.replicate n (List.map signedFreeRelLetter word)).flatten` `but is expected to have type` `@Eq (List (RelLetter (FreeGroup Generator) PEmpty.{1})) C.toDeletion.replacement.diagram.boundaryWord (List.replicate n (List.map signedFreeRelLetter word)).flatten` |
| `GGT.DGOLemma421FourGon` | **NO** | 0 | `GroupApproximation/GGT/DGOLemma421FourGon.lean:35:10: Function expected at` `wordDist` `but this term has type` `?m.1` `... Hint: The identifier \`wordDist\` is unknown, and Lean's \`autoImplicit\` option causes an unknown identifier to be treated as an implicitly bound variable ...` |
| `KTheory.Basic` | **YES** | 0 | — |
| `KTheory.Functorial` | **YES** | 0 | — |
| `KTheory.Spaces` | **NO** | 0 | `GroupApproximation/KTheory/Spaces.lean:43:4: failed to compile definition, consider marking it as 'noncomputable' because it depends on 'instCommCStarAlgebraComplex', which is 'noncomputable'` |

**10 of 14 compile clean. 4 fail.** Total sorry count across all 14, by Lean's own
report: **2**, both in one file (`KazhdanHypGirthEightGenericProducers.lean`).

## Notes per section of the assignment

### STW22 factorial-pair chain — status has CHANGED since the sweep note

**All four now compile, including `STW22TraciallyCompletePair`.** The sweep note's
`STW22TraciallyCompletePair.lean:80` (unreferenced `σ`) and `:268` (type mismatch)
are gone: `git log -3 --oneline -- Analysis/STW22TraciallyCompletePair.lean` shows
`3ef11dd25 xxii: route realize 0 = 0 through the isolated defeq lemma` as the most
recent real edit, already on `origin/main` (confirmed: the file's current content
is byte-identical to `origin/main:ca19a87d0`). This matches lane `xxii-fix`'s
assignment to repair exactly this chain — **coordinated, not collided**: I built
against what's already landed and did not touch these four files myself. Whether
`xxii-fix` considers its own fix complete or still in progress is for them to say;
what I can confirm is that as of `ca19a87d0` the chain builds clean end to end,
including the two downstream files (`AntipodalGaugeFactorial`,
`AntipodalFactorialPair`) that could only build if `TraciallyCompletePair` itself
is now sound.

### The four "still wired" files — confirmed, not assumed

`STW22CounterexampleCompactnessRoute`, `STW22FibreEvaluation`,
`DGOProposition414SecondSeparationHalfWord`, `HullSCLemma44PrefixKernelCutConstruction`
all compile clean as explicit targets, independently of the root build. None
appear in `lake`'s failure list; none produced any error or sorry line.

### The three previously-unwired GGT files — depth assessment

* **`KazhdanHypGirthEightGeodesicWord`** — shallow-looking, one error site: a
  single `rewrite` whose pattern (`wordDist ?S ?x ?x`) isn't found in the current
  goal shape (`OsinComponents.IsGeodesicWord D x.val x.val word`). Consistent with
  API drift in how `IsGeodesicWord`/`wordDist` relate now versus when this file
  (dated 2026-09-02) was written, not obviously a broken proof strategy. No sorry.
* **`KazhdanHypGirthEightGenericProducers`** — deep. Errors at eight distinct
  points (lines 63, 78, 84, 87, 146, 160, 162, 179, 181, 185) spanning several
  declarations: type mismatches, an application expecting a `Prop` given a
  non-`Prop`, two `omega` failures, and two declarations whose elaboration failed
  outright and were papered over with `sorry` (84, 87) — confirming the sweep
  note's hypothesis that these are elaborator-inserted recovery, not
  author-written admissions, since they sit alongside independently-reported type
  errors in the same neighbourhood. This is not a rename; the file has drifted
  substantially from its dependencies.
* **`DGOLemma421FourGon`** — deeper than shallow, not as deep as
  `GenericProducers`. Two unknown identifiers repeat as a pattern:
  `wordDist` (lines 35, 39 — same missing name `KazhdanHypGirthEightGeodesicWord`
  hit at line 115, suggesting a **shared root cause** worth investigating
  together rather than as two unrelated breaks) and `isGeodesicWord_one_of`
  (lines 46, 48), plus `isQuasiGeodesicPolygon_translate` (line 86) and four
  further type mismatches (56, 59, 78, 79) that look like consequences of the
  missing identifiers rather than independent breaks. No sorry.

**Correction to the assignment's framing, stated plainly rather than silently
matched to it**: the assignment said "two of them carry sorry." Lean's own report
says otherwise — exactly **one** of the three files (`GenericProducers`) carries
sorry (two instances, both inside it); `GeodesicWord` and `DGOLemma421FourGon`
carry none. Reporting the discrepancy rather than rounding my count to fit the
expectation.

### KTheory/{Basic,Functorial,Spaces} — the author's caution was partially warranted

`Basic` and `Functorial` compile clean. `Spaces` does not, and the failure is
shallow and specific: `Spaces.lean:43` defines something that needs
`noncomputable` because it transitively depends on
`instCommCStarAlgebraComplex`, itself noncomputable — a one-line fix
(`noncomputable def`/`noncomputable instance`) if the definition doesn't need to
compute, which is the normal fix for this exact Lean message. Not the kind of
error a "UNPROBED, do not import yet" caution is usually protecting against
(no sorry, no type-theoretic gap, no drift against a moved dependency) — it reads
like the file was written and never actually run through the compiler once, and
the very first thing a probe would have caught is this one missing keyword.
Whether the separate KK-theory/Kasparov apparatus under `Analysis/` makes this
chain redundant is a judgment call outside what a build can answer, unchanged
from the sweep note.

## Raw sorry-line extraction (Lean's report, not a grep)

```
$ grep -n "declaration uses" <probe-log>
170:error: GroupApproximation/GGT/KazhdanHypGirthEightGenericProducers.lean:87:6: declaration uses `sorry`
171:error: GroupApproximation/GGT/KazhdanHypGirthEightGenericProducers.lean:84:8: declaration uses `sorry`
```

Two lines, zero elsewhere across all fourteen files' build output.

## What was not done

No file was edited, fixed, wired, or unwired. `GroupApproximation.lean` was not
touched. No coordination action taken with `xxii-fix` beyond building against
whatever is currently on `origin/main` (the honest thing to confirm, per the
assignment).
