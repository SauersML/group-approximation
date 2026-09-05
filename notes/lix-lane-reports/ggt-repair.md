# ggt-repair

Repair lane for the red root build caused by commit `fadb6fd6d` ("WIP GGT:
carry a boundary-cycle rotation in RelativeBoundaryContiguity"), which added
a `rotation : ℕ := 0` field to `RelativeBoundaryContiguity` and changed
`boundary_decomposition` from `boundaryWord = before ++ arc ++ after` to
`boundaryWord.rotate rotation = before ++ arc ++ after`.

Owned exactly four files (per lead assignment): `HullSCLemma44EmbeddedCertificate.lean`,
`HullSCLemma44RelativeDehn.lean`, `HullSCLemma44CertificateInjectivity.lean`,
`HullSCLemma49Correction.lean`.

## GREEN

`ccprobe.sh ggt-repair` on the four owned modules:

```
Build completed successfully (9785 jobs).
```

Two separate runs, both clean (`ERROR_LINES=0`).

## What changed, per file

- **HullSCLemma44EmbeddedCertificate.lean** (`of_embeddedData`, the `B0`
  literal around line 222): the field literal built a
  `RelativeBoundaryContiguity` from an *unrelated* structure's own
  (unrotated) `EmbeddedBoundaryPosition.boundary_decomposition`. Pinned
  `rotation := 0` explicitly and discharged the field with
  `by rw [List.rotate_zero]; exact data.position.boundary_decomposition`.
  (The `Embedded.Contiguity.boundary_decomposition` used earlier in the same
  file, line 96, is a different, untouched structure — left alone.)

- **HullSCLemma44RelativeDehn.lean** — the file with the "load-bearing"
  semantic break the commit called out:
  - `map_shortenedBoundaryWord_prod_eq` and
    `boundaryWord_prod_eq_conjugate_relator_mul_shortened` each gained a new
    explicit hypothesis `(hrot : C.rotation = 0)`, and their internal
    `congrArg List.prod C.boundary_decomposition` step now goes through
    `C.boundary_decomposition_of_rotation_zero hrot` (the compatibility lemma
    fadb6fd6d already added). This is unavoidable: for `rotation ≠ 0` in a
    nonabelian group, `boundaryWord.prod` is only a *conjugate* of
    `before.prod * arc.prod * after.prod`, not equal to it, so the old
    unconditional statement is now false in general.
  - `shortenedBoundaryWord_length_lt`: the `omega` call failed because
    `hboundaryLength` carried the atom `(boundaryWord.rotate C.rotation).length`
    instead of `boundaryWord.length`. Fixed by adding `List.length_rotate` to
    the `simp only` set feeding `omega` (rotation preserves length, no `hrot`
    needed).
  - `shortenedBoundaryWord_isWord` (two membership goals,
    `x ∈ C.boundaryBefore`/`C.boundaryAfter` ⟹ `x ∈ boundaryWord`): replaced
    the direct `rw [C.boundary_decomposition]` with
    `apply (List.mem_rotate (n := C.rotation)).mp` first, then the same
    `rw`+`exact` as before. No `hrot` needed — membership is rotation-invariant.
  - `replacementWord_length_lt_boundaryArc_of_certificate` (`harcWord`): the
    membership goal `x ∈ K.boundaryWord` from `hx : x ∈ C.boundaryArc` is
    exactly `RelativeBoundaryContiguity.boundaryArc_mem_boundaryWord`
    (fadb6fd6d's own compatibility lemma) — swapped in directly, no `hrot`.
  - `exists_relativeDehnCut_of_certificate` and `exists_relativeDehnCut_of_kernel`
    (the only internal callers of `map_shortenedBoundaryWord_prod_eq`) each
    gained a new trailing hypothesis
    `(hrot : ∀ {i} {C}, K.contiguity i = some C → C.rotation = 0)`
    and thread it to the certificate's `quotient_value` field. This is a
    genuine, unavoidable interface change (see TRAPS below).

- **HullSCLemma44CertificateInjectivity.lean** (`false_of_relativeDiagramCertificate`):
  the only two uses of `boundary_decomposition` (`harcWord`, `harcLength`)
  were purely membership/length facts, not value facts. Dropped the
  intermediate `hboundaryDecomposition : Z.boundaryWord = before++arc++after`
  entirely and rewired both `have`s through the two compatibility lemmas
  (`boundaryArc_mem_boundaryWord`, `boundaryArc_length_le_boundaryWord`).
  No `hrot` needed. (Trap while doing this — see below.)

- **HullSCLemma49Correction.lean** (`exists_boundaryArc_source`): this one's
  conclusion was a genuine *exact* list decomposition
  (`boundary = pre ++ arc ++ suf`, not `.prod` equality), which is also false
  under rotation. Since `List.map_rotate` commutes rotation with `List.map`,
  restated the conclusion as `boundary.rotate C.rotation = pre ++ arc ++ suf`
  (true unconditionally, and defeq to the old statement at `rotation = 0` via
  `List.rotate_zero`) instead of adding `hrot`. This is the "explicit
  rotated form" alternative the commit message offered, applied where it
  costs nothing.

## TRAPS

- **`K.boundaryWord_eq` is not syntactically `Z.boundaryWord`.** In
  `HullSCLemma44CertificateInjectivity.lean`, `K : RelativeDiagramCertificate
  D W eps mu (Z.toRelativeReducedDiagram D)` where `Z :
  Lemma44OrientedRelatorDiagram …`. `K.boundaryWord_eq` has the literal type
  `K.boundaryWord = (Z.toRelativeReducedDiagram D).boundaryWord`, which is
  only *defeq* (not syntactically equal) to `K.boundaryWord = Z.boundaryWord`
  — the goal displays the latter. `rw [← K.boundaryWord_eq]` therefore fails
  with "did not find an occurrence" even though the term is fine in `exact`
  position. Fix: `have hbw : K.boundaryWord = Z.boundaryWord :=
  K.boundaryWord_eq` (the `have`'s ascribed type re-syntaxes it via defeq
  elaboration), then `rw [← hbw]` matches.
- **A missing last argument can surface two lines later as `motive is not
  type correct`, not "missing argument".** Confirmed against
  `HullSCLemma44RelativeBoundary.lean:161-162` (not ours, unfixed): its call
  `exists_relativeDehnCut_of_kernel D hsc hmu hrho K q hker` now omits the
  new `hrot` argument. Because the theorem's conclusion doesn't mention
  `hrot`, Lean happily elaborates `hcut` as a still-curried function
  `(∀ {i} {C}, …) → Nonempty (RelativeDehnCut …)` instead of flagging the
  missing argument — and the *next* line's `rw [K.boundaryWord_eq, …] at
  hcut` then dies with "motive is not type correct" (rewriting
  `K.boundaryWord` under a Pi-type whose domain and codomain both mention
  it). Anyone fixing the residue below should expect this exact error shape
  and know the real fix is supplying `hrot`, not touching the `rw`.

## Residue for a follow-up lane (NOT fixed — outside the four owned files)

Adding `hrot` to `exists_relativeDehnCut_of_certificate` /
`exists_relativeDehnCut_of_kernel`, and rotating `exists_boundaryArc_source`'s
conclusion, are forced, correct, and unavoidable — but both are genuine public
interface changes to declarations from `HullSCLemma44RelativeDehn.lean` and
`HullSCLemma49Correction.lean` that ripple into files this lane does not own.
Probed the 15 files that textually reference the four owned modules
(`ccprobe.sh ggt-repair` on all 15 as extra targets, same clone, 9940 jobs
attempted): confirmed broken —

- `HullSCLemma44RelativeBoundary.lean:161-162` — missing `hrot` at the
  `exists_relativeDehnCut_of_kernel` call (see TRAPS).
- `HullSCLemma44KernelGeodesicCut.lean:52` — unsolved goal, same missing-`hrot`
  shape at its `exists_relativeDehnCut_of_certificate` call.
- `HullSCLemma49FromRelativeGreendlinger.lean:149` — consumes
  `exists_boundaryArc_source`; `hsplit` is now typed
  `(…).rotate Cpower.rotation = pre ++ arc ++ suf` where the caller expects
  the unrotated form. Needs the same rotate-back treatment we gave
  `exists_boundaryArc_source` itself, or a `Cpower.rotation = 0` fact.
- `HullSCLemma44PrefixCutRatio.lean:134` — an independent, pre-existing
  "tactic break" (plain `rw [C.boundary_decomposition]` on a membership goal),
  exactly the same shape as the ones fixed in this lane's four files. Trivial
  with the same `mem_rotate`/compatibility-lemma pattern.

Confirmed still green (built clean in the same probe, unaffected):
`HullSCLemma44RelativeCertificateAdapter.lean`, `HullSCLemma44PrefixCut.lean`.

Unreached/unknown in this probe (blocked behind the four failures above, so
lake never attempted them — not yet independently confirmed red or green
once the four are fixed): `HullSCLemma44RelativeArea.lean`,
`HullSCLemma44WeightedArea.lean`, `HullSCLemma44MixedArea.lean`,
`HullSCLemma44FamilyAssembly.lean`, `HullSCLemma44KernelAssembly.lean`,
`HullSCLemma44Canonical.lean`, `HullSCLemma49Assemble.lean`,
`HullSCLemma49PrimePiece.lean`, `HullSCLemma49ShortPower.lean`,
`HullSCRelativeGreendlingerBoundaryArc.lean`,
`HullSCRelativeGreendlingerGeodesicConsumers.lean`. `RelativeArea.lean` and
`WeightedArea.lean` in particular each call
`boundaryWord_prod_eq_conjugate_relator_mul_shortened` /
`map_shortenedBoundaryWord_prod_eq` directly on a `C` obtained from an
existential (`K.largeCell`/`RelativeBoundaryContiguity.exists_ratio_bounded_cut_of_certificate`)
that carries no rotation information, so they will need the same `hrot`
threading once reached.

This is a strictly larger blast radius than the four files originally
assigned; none of it was fixable from inside those four files alone (the
needed `C.rotation = 0` facts live in structures — `RelativeDiagramCertificate.largeCell`,
etc. — this lane does not own), so it is left as an honest, itemized
follow-up rather than papered over.
