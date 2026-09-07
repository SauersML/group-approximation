# Lane `ring-b-end` — the endpoint of Theorem 2 and its two corollaries

Scope: `thm:full-defect-ring`, `cor:simple-infinite-ring`,
`cor:one-sided-ring-maximal` of `non_mf_groups_exist.tex`.
Sub-namespace: `GroupApproximation.Manuscript.OneSidedMFRadical.FullDefectRing`.

## Landed

| commit | jobs | modules, all under `Manuscript/OneSidedMFRadical/` |
|---|---|---|
| `8c21918e938f952350c45afa440040cefb700935` | 4070 | `FullDefectRingCore.lean` |
| `bc49957918c4f4cb5d768d190c65a4d59ef7d92c` | 3444 | `FullDefectRingDescent.lean`, `FullDefectRingFullIdeal.lean` |
| `443c2e380b9a9092d2ba40f92c9195c08b340798` | 4253 | `FullDefectRingCountable.lean` |
| `36b7fb0010b1b677c3ba58a311f1f04ca6007e1d` | 4257 | `FullDefectRingSimple.lean` |
| `1dd5b6630fcab4116b709f1d0625e8c718be6b5a` | 4257 | `FullDefectRingMaximal.lean` |
| `0c2cfacd517265f4df77bb30863b356694dbb881` | 4262 | `FullDefectRingEndpoints.lean` |
| `aabd8e02b344687e0de71d79fe4c478d512d0700` | 4267 | `FullDefectRingProperIsometry.lean` |
| `bdd935ede3ef52efd781cfc0deadbc4618020b42` | 4273 | `FullDefectRingUnconditional.lean` |
| `c1bf110bff38c4ccf861f2f14641b643bd5cd3e3` | 4277 | `FullDefectRingStrictness.lean` |

## The printed clauses, and what each still assumes

`fullDefectAtFixedRing` (lane `ring-b-alg`,
`Leavitt/FullDefectRingAtFixedRing.lean`, commit `3f69392c9`) discharged the
compression calculation, so every clause below is either unconditional or
carries a single named hypothesis.

| printed | proposition | hypothesis-free form |
|---|---|---|
| `thm:full-defect-ring` | `PrintedFullComplementaryIdempotents` | over prime characteristic |
| sentence after it | `PrintedFullnessHolds` | yes, always |
| `cor:simple-infinite-ring`, 1st | `PrintedSimpleInfiniteRing` | over prime characteristic |
| `cor:simple-infinite-ring`, 2nd | `PrintedLeavittAlgebraFullDefect` | over prime characteristic |
| `cor:one-sided-ring-maximal`, 2nd | `PrintedOneSidedRingMaximalReducedCStar` | over prime characteristic |
| `cor:one-sided-ring-maximal`, 1st | `PrintedOneSidedRingMaximalIsometry` | over prime characteristic |

Outside prime characteristic each carries exactly one leading hypothesis,
`FinitelyGeneratedRingGeneralRankElementaryPropertyT`, which is lane
`ejz-integral`'s.

## Module by module

### `FullDefectRingCore`

* `SaturatedPrintedDefectRadical` / `manuscriptSaturatedPrintedDefectRadical`
  (`#audit_closed_axioms`) — the last step of the printed proof, with no ring in
  it: countable `G`, `L ≤ G` with `(T)`, `(T)` for `G`, and
  `printedDefect L = ⊤` give the full MF radical in both readings, triviality
  of every homomorphism to an MF group, and `¬ IsCDEOperatorMF G` for
  nontrivial `G`.  This is the interface `ring-b-alg` consumes.
* `countable_elementaryGroup`.

### `FullDefectRingDescent`

The printed "general countable `R`" paragraph, as pure group theory.
`subringElementary`, `subringElementary_le_map`,
`elementaryGroup_le_finiteCoefficientSubgroup`,
`exists_finset_elementaryGroup_le_map`,
`isFinitelyGeneratedRing_subringClosure`.

### `FullDefectRingFullIdeal`

`exists_sum_eq_one_of_isSimpleRing`, `isSimpleRing_full_of_not_directlyFinite`,
`leavittFamily_full`, `completeMatrixFamily_full`.

### `FullDefectRingCountable`

`FullDefectAtFixedRing`;
`PrintedFullComplementaryIdempotentsOverSubrings` (the sharpest form, property
`(T)` asked only of the finitely generated subrings);
`PrintedFullComplementaryIdempotents`;
`PrintedFullComplementaryIdempotentsPrimeChar`.

### `FullDefectRingSimple`

`exists_oneSidedInverse_of_not_isDedekindFinite`; `PrintedSimpleInfiniteRing`,
`PrintedLeavittAlgebraFullDefect` and their `...PrimeChar` forms.

### `FullDefectRingMaximal`

`nontrivial_elementaryGroup`, `not_isCDEOperatorMF_of_killsMFTargets`;
`PrintedOneSidedRingMaximalReducedCStar` and its `...PrimeChar` form.

### `FullDefectRingProperIsometry`

`properIsometry_of_strictCompression`,
`OneSidedCompressorStrictContainment`, `PrintedOneSidedRingMaximalIsometry` and
its `...PrimeChar` form.

### `FullDefectRingEndpoints`

`PrintedFullnessHolds` / `manuscriptPrintedFullnessHolds`
(`#audit_closed_axioms`); `PrintedFullDefectRingProgramme` and its
`...PrimeChar` form.

### `FullDefectRingStrictness`

`leftFixSubgroup E` — the elementary matrices with `E g = E`, a subgroup for
reasons unrelated to elementary matrices — together with
`coreOverHom S hn`, the image of `EL₃(S)` in `EL_n(R)`, and `defectCorner`, the
complementary idempotent at the first compressor coordinate.  One induction
(`conj_mem_range_inf`) puts every conjugate simultaneously in the range and in
`leftFixSubgroup`, which gives `compressorOf_strict` and then
`manuscriptOneSidedCompressorStrictContainment` (`#audit_closed_axioms`).
Property `(T)` for the image is free from `MonoidHom.rangeRestrict_surjective`,
which is what makes `S` rather than `R` costless.

### `FullDefectRingUnconditional`

Spends `fullDefectAtFixedRing` once, and names each printed clause in its two
remaining forms: `manuscript...PrimeCharUnconditional` (hypothesis-free, all
audited closed) and `manuscript...FromEJZ` (one hypothesis).  The
proper-isometry clause is spent the same way inside `FullDefectRingStrictness`,
because that is where its input is proved.

## Open obligations

One, and it is not this lane's mathematics:
`FinitelyGeneratedRingGeneralRankElementaryPropertyT`, lane `ejz-integral`.
Every clause outside prime characteristic carries it, and nothing else.

The compression calculation (`FullDefectAtFixedRing`, discharged by
`ring-b-alg`'s `fullDefectAtFixedRing`) and the strictness of the compression
(`OneSidedCompressorStrictContainment`, discharged here by
`manuscriptOneSidedCompressorStrictContainment`) are both closed.

## Coordination note

`ring-b-alg` and this lane both wrote the rank-four-to-rank-`n` extension and
the seam that discharges `FullDefectAtFixedRing`.  Theirs landed; the copy
written here was deleted unlanded rather than renamed, because a same-content
declaration under a different name is what the duplicate scan cannot see.
