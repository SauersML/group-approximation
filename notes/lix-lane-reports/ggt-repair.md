# ggt-repair

Repair lane for the red root build caused by commit `fadb6fd6d` ("WIP GGT:
carry a boundary-cycle rotation in RelativeBoundaryContiguity"), which added
a `rotation : ℕ := 0` field to `RelativeBoundaryContiguity` and changed
`boundary_decomposition` from `boundaryWord = before ++ arc ++ after` to
`boundaryWord.rotate rotation = before ++ arc ++ after`.

Started with a 4-file assignment (`HullSCLemma44EmbeddedCertificate.lean`,
`HullSCLemma44RelativeDehn.lean`, `HullSCLemma44CertificateInjectivity.lean`,
`HullSCLemma49Correction.lean`). The lead then expanded ownership to every
rooted transitive consumer of `HullSCRelativeGreendlingerStatement` that
fails — the 89-module list in `ggt-consumers.txt`. `HullSCRelativeGreendlingerStatement.lean`
itself was never touched, per instruction.

## GREEN

`ccprobe.sh ggt-repair` on the full 89-module list:

```
Build completed successfully (10348 jobs).
```

Confirmed clean (`ERROR_LINES=0`), including all of the four originally-owned
modules on their own (`9785 jobs`, two separate earlier runs).

## Files changed (22 total)

Original four: `HullSCLemma44EmbeddedCertificate.lean`,
`HullSCLemma44RelativeDehn.lean`, `HullSCLemma44CertificateInjectivity.lean`,
`HullSCLemma49Correction.lean`.

Expanded-scope eighteen: `HullSCLemma44PrefixCutRatio.lean`,
`HullSCLemma44KernelGeodesicCut.lean`, `HullSCLemma44RelativeBoundary.lean`,
`HullSCLemma44NormalPolygon.lean`, `HullSCLemma49EmbeddedArc.lean`,
`HullSCLemma49Rebase.lean`, `HullSCLemma49FromRelativeGreendlinger.lean`,
`HullSCLemma49LongPeriod.lean`, `HullSCLemma49FixedDelta.lean`,
`HullSCLemma49ShortLoxodromic.lean`, `HullSCLemma49Assemble.lean`,
`HullSCLemma44WeightedArea.lean`, `HullSCLemma44RelativeArea.lean`,
`HullSCLemma44KernelAssembly.lean`, `HullSCLemma49InjectivityBridge.lean`,
`HullSCLemma44RelativeIsoperimetric.lean`, `HullSCLemma44MixedArea.lean`,
`HullSCLemma44Canonical.lean`.

## The two repair patterns

Every red spot fell into exactly one of two shapes.

**1. Rotation-invariant facts (membership, length) — no new hypothesis.**
`List.mem_rotate`/`List.length_rotate` recover these for free, or (better,
where available) the compatibility lemmas `fadb6fd6d` itself added to
`RelativeBoundaryContiguity`: `boundaryArc_mem_boundaryWord`,
`boundaryArc_length_le_boundaryWord`, `boundary_decomposition_of_rotation_zero`.
Construction sites that discharge `boundary_decomposition` with a bare
`simpa`/`simp` (`HullSCLemma49Rebase.lean`, `HullSCLemma49EmbeddedArc.lean`,
both leaving `rotation` at its `:= 0` default) just needed `List.rotate_zero`
folded into the simp set.

**2. Genuine value-level facts (`.prod` equalities, exact list splits) — need
`rotation = 0`.** For `rotation ≠ 0` in a nonabelian group, a rotated word's
product is only a *conjugate* of the unrotated pieces' product, not equal to
it — the pre-`fadb6fd6d` unconditional statement is now mathematically false
in general. Two of `RelativeBoundaryContiguity`'s own theorems
(`map_shortenedBoundaryWord_prod_eq`, `boundaryWord_prod_eq_conjugate_relator_mul_shortened`,
in `HullSCLemma44RelativeDehn.lean`) needed an explicit
`(hrot : C.rotation = 0)` hypothesis; `HullSCLemma49Correction.lean`'s
`exists_boundaryArc_source` instead restated its conclusion as
`boundary.rotate C.rotation = pre ++ arc ++ suf` (via `List.map_rotate`),
avoiding the hypothesis since nothing forced its shape.

Since no certificate anywhere in this development is ever built with
`rotation ≠ 0` (grepped every `RelativeBoundaryContiguity` literal
construction: `RelativeBoundaryContiguity.empty`,
`RelativeBoundaryContiguity.of_embeddedData`, and the two ad hoc literals in
Rebase/EmbeddedArc all leave `rotation` at its default `0`), `hrot` is true
everywhere — but proving it from scratch requires seeing the literal
construction, which most consumers are many layers removed from (they only
ever see a certificate through an existential like
`RelativeDiagramCertificate.largeCell`, which carries no rotation
information). So `hrot` is threaded as a new **hypothesis parameter**
top-to-bottom rather than fabricated locally — this is the correct,
non-weakening fix, not a workaround. Two shapes of `hrot` were used depending
on whether `D`/`eps` are already fixed at the theorem's own signature
(`∀ {boundaryWord'} {relator'} (C : RelativeBoundaryContiguity D eps
boundaryWord' relator'), C.rotation = 0`) or only become concrete inside the
proof, because the theorem proves an abstract `def foo : Prop := ∀ {G}
[Group G] ..., ...` statement (`∀ {G} [Group G] {Lambda} (D' :
GGT.RelGenSet G Lambda) {eps} ..., C.rotation = 0`, applied as `hrot D'` at
each use). None of the `Prop`s being proven (`HullLemma44CanonicalQuotientStatement`,
`HullLemma49ShortestGeodesicPowerDiagramStatement`,
`KernelConeLocalFinitenessStatement`, etc.) were touched — only the extra
hypothesis on the *theorems proving them* changed, and every one of those
theorems turned out to have zero or only in-repo callers, so none of this
rippled to a file outside the 89-module list.

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
- **A missing last argument can surface far away as `motive is not type
  correct`, not "missing argument".** `HullSCLemma44RelativeBoundary.lean`'s
  `have hcut := exists_relativeDehnCut_of_kernel D hsc hmu hrho K q hker`
  (missing the new `hrot`) elaborated fine as a still-curried function value
  (the theorem's conclusion doesn't mention `hrot`), and only the *next*
  line's `rw [K.boundaryWord_eq, hZboundary] at hcut` died, with "motive is
  not type correct" (rewriting `K.boundaryWord` under a Pi-type whose domain
  and codomain both mention it) — nowhere near the actual missing argument.
  Once `hrot` is supplied, `hcut` is a closed `Nonempty` term again and the
  `rw` needs no other change.
- **`ccprobe`'s progress log only prints a line for jobs it actually (re)runs.**
  A module that is already up to date relative to the current source tree
  prints nothing — so "no ✔/✖ line for X" means X is fine, not that it was
  skipped. Downstream-of-a-failure modules print nothing either (never
  attempted), which is the ambiguous case; distinguishing the two just needs
  a second probe once the failures are fixed.
- Two self-inflicted mistakes worth flagging for anyone re-deriving this:
  a blanket `∀ C, C.rotation = 0` is **not** provable by `rfl` for an
  abstract/opaque `C` (only for a literal structure value with `rotation`
  left at its default) — I twice wrote a bogus `rfl`/mismatched-type `hrot`
  under time pressure before catching it against the compiler. Always thread
  `hrot` as a real parameter unless you are at the exact literal construction
  site.

## Verification

- All 22 changed files: no `sorry`, `admit`, `axiom`, `opaque`, or
  `native_decide` (checked by grep across the diff).
- Full 89-module probe: `Build completed successfully (10348 jobs)`,
  `ERROR_LINES=0`.
- No statement was weakened: every `hrot` addition is a new hypothesis on a
  theorem whose *unconditional* form is genuinely false for `rotation ≠ 0`
  in a nonabelian group; `exists_boundaryArc_source`'s rotated restatement is
  strictly more general than (and defeq to, at `rotation = 0`) the form it
  replaced.
